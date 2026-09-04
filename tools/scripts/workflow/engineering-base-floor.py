#!/usr/bin/env python3
"""Derive and verify the protected-base engineering execution floor."""

from __future__ import annotations

import argparse
import json
import posixpath
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


def git(repository: Path, *arguments: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(repository), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def local_name(element: ET.Element) -> str:
    return element.tag.rsplit("}", 1)[-1]


@dataclass(frozen=True)
class Project:
    path: str
    assembly: str
    is_test: bool
    references: tuple[str, ...]
    compile_includes: tuple[str, ...]

    @property
    def directory(self) -> str:
        return self.path.rsplit("/", 1)[0]


def child_text(root: ET.Element, name: str) -> list[str]:
    return [
        (element.text or "").strip()
        for element in root.iter()
        if local_name(element) == name and (element.text or "").strip()
    ]


def resolve_item(project_path: str, include: str) -> str:
    return posixpath.normpath(posixpath.join(project_path.rsplit("/", 1)[0], include.replace("\\", "/")))


def read_projects(repository: Path, base: str) -> tuple[str, list[Project]]:
    base_sha = git(repository, "rev-parse", "--verify", f"{base}^{{commit}}").decode().strip()
    paths = git(repository, "ls-tree", "-r", "-z", "--name-only", base_sha, "--", "tools")
    projects: list[Project] = []
    for raw_path in paths.split(b"\0"):
        if not raw_path:
            continue
        path = raw_path.decode("utf-8", errors="strict")
        if not path.endswith(".csproj"):
            continue
        # Every topology byte comes from the protected base; no base checkout or build occurs.
        content = git(repository, "show", f"{base_sha}:{path}")
        root = ET.fromstring(content)
        is_xunit = any(
            local_name(element) == "PackageReference"
            and element.attrib.get("Include") == "xunit"
            for element in root.iter()
        )
        classifications = {value.casefold() for value in child_text(root, "IsTestProject")}
        is_test = is_xunit or classifications == {"true"}
        assembly = next(
            iter(child_text(root, "AssemblyName")),
            Path(path).stem,
        )
        references = tuple(sorted({
            resolve_item(path, element.attrib["Include"])
            for element in root.iter()
            if local_name(element) == "ProjectReference" and element.attrib.get("Include", "").strip()
        }))
        compile_includes = tuple(sorted({
            resolve_item(path, include)
            for element in root.iter()
            if local_name(element) == "Compile"
            for include in element.attrib.get("Include", "").split(";")
            if include.strip() and "$(" not in include
        }))
        projects.append(Project(path, assembly, is_test, references, compile_includes))

    if not any(project.is_test for project in projects):
        raise RuntimeError("protected-base topology derived zero test projects")
    folded = [project.assembly.casefold() for project in projects if project.is_test]
    if len(folded) != len(set(folded)):
        raise RuntimeError("protected-base topology contains duplicate test assembly identities")
    return base_sha, sorted(projects, key=lambda project: project.path)


def glob_covers(pattern: str, path: str) -> bool:
    expression = re.escape(pattern)
    expression = expression.replace(r"\*\*/", "(?:.*/)?")
    expression = expression.replace(r"\*", "[^/]*").replace(r"\?", "[^/]")
    return re.fullmatch(expression, path) is not None


def required_projects(repository: Path, base: str, head: str, full: bool) -> list[Project]:
    base_sha, projects = read_projects(repository, base)
    tests = [project for project in projects if project.is_test]
    if full:
        return tests
    changed = git(
        repository,
        "diff",
        "--name-only",
        "-z",
        "--no-renames",
        base_sha,
        head,
        "--",
    ).split(b"\0")
    affected: set[str] = set()
    for raw_path in changed:
        if not raw_path:
            continue
        path = raw_path.decode("utf-8", errors="strict")
        owners = [
            project
            for project in projects
            if path == project.path
            or path.startswith(project.directory + "/")
            or any(glob_covers(pattern, path) for pattern in project.compile_includes)
        ]
        if not owners:
            return tests
        owner = sorted(
            owners,
            key=lambda project: (
                -(len(project.directory) if path.startswith(project.directory + "/") else 0),
                project.path,
            ),
        )[0]
        affected.add(owner.path)
    while True:
        before = len(affected)
        affected.update(
            project.path
            for project in projects
            if any(reference in affected for reference in project.references)
        )
        if len(affected) == before:
            break
    return [project for project in tests if project.path in affected]


def require_nonempty_floor(required: list[object]) -> None:
    if not required:
        raise RuntimeError(
            "ENGINEERING_BASE_FLOOR_EMPTY protected-base has test projects; "
            "an empty required set must be explicitly declared rather than silently admitted"
        )


def prepare(arguments: argparse.Namespace) -> int:
    repository = Path(arguments.repository).resolve(strict=True)
    projects = required_projects(
        repository,
        arguments.base,
        arguments.head,
        arguments.full == "1",
    )
    require_nonempty_floor(projects)
    results_directory = Path(arguments.results_directory).resolve()
    if results_directory.exists():
        shutil.rmtree(results_directory)
    results_directory.mkdir(parents=True)
    assemblies = [project.assembly for project in projects]
    with open(arguments.github_output, "a", encoding="utf-8", newline="\n") as output:
        output.write("required_assemblies_json=")
        output.write(json.dumps(assemblies, ensure_ascii=True, separators=(",", ":")))
        output.write("\n")
        output.write("required_projects_json=")
        output.write(json.dumps([project.path for project in projects], ensure_ascii=True, separators=(",", ":")))
        output.write("\n")
    for project in projects:
        print(
            f"ENGINEERING_BASE_FLOOR_REQUIRED assembly={project.assembly} "
            f"project={json.dumps(project.path)} source=protected-base"
        )
    # This is a lower bound over base topology. Candidate-added tests remain candidate-owned.
    print(f"ENGINEERING_BASE_FLOOR_READY assemblies={len(assemblies)}")
    return 0


def executed_assemblies(results_directory: Path) -> Counter[str]:
    trx_files = sorted(results_directory.rglob("*.trx"))
    if not trx_files:
        raise RuntimeError("engineering produced no TRX evidence")
    executed: Counter[str] = Counter()
    for trx_file in trx_files:
        root = ET.parse(trx_file).getroot()
        results = {
            result.attrib.get("testId"): result
            for result in root.iter()
            if local_name(result) == "UnitTestResult" and result.attrib.get("testId")
        }
        for test in (element for element in root.iter() if local_name(element) == "UnitTest"):
            result = results.get(test.attrib.get("id"))
            if result is None or result.attrib.get("outcome") == "NotExecuted":
                continue
            storage = test.attrib.get("storage")
            if not storage:
                raise RuntimeError(f"TRX test has no assembly identity: {trx_file}")
            executed[Path(storage).stem.casefold()] += 1
    return executed


def verify(arguments: argparse.Namespace) -> int:
    required = json.loads(arguments.required_assemblies_json)
    if not isinstance(required, list) or any(
        not isinstance(item, str) or not item.strip() for item in required
    ):
        raise RuntimeError("required assembly output is not a string array")
    require_nonempty_floor(required)
    evidence = executed_assemblies(Path(arguments.results_directory).resolve(strict=True))
    for assembly in required:
        count = evidence[assembly.casefold()]
        if count == 0:
            raise RuntimeError(f"TRX has no executed identity from required assembly {assembly}")
        print(
            f"ENGINEERING_BASE_FLOOR_EXECUTED assembly={assembly} "
            f"evidence=trx executed={count}"
        )
    # Candidate controls these bytes, so this detects omission but cannot prove non-forgery.
    print(f"ENGINEERING_BASE_FLOOR_VERIFIED assemblies={len(required)} evidence=trx")
    return 0


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare_parser = subparsers.add_parser("prepare")
    prepare_parser.add_argument("--repository", required=True)
    prepare_parser.add_argument("--base", required=True)
    prepare_parser.add_argument("--head", required=True)
    prepare_parser.add_argument("--full", choices=("0", "1"), required=True)
    prepare_parser.add_argument("--github-output", required=True)
    prepare_parser.add_argument("--results-directory", required=True)
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("--required-assemblies-json", required=True)
    verify_parser.add_argument("--results-directory", required=True)
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    try:
        return prepare(arguments) if arguments.command == "prepare" else verify(arguments)
    except (ET.ParseError, OSError, RuntimeError, ValueError, json.JSONDecodeError) as exception:
        print(f"ENGINEERING_BASE_FLOOR_FAILED {exception}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
