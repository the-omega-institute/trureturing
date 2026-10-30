"""Lake dependency checkout boundaries for registered worktree removal."""


class LakeNestedGitCases:
    def lake_dependency(self, project, package):
        boundary = project / ".lake/packages" / package
        boundary.mkdir(parents=True)
        self.g(boundary, "init")
        return boundary

    def declare_lake_package(self, project, package):
        (project / "lake-manifest.json").write_text(
            '{"packages":[{"name":"' + package + '"}]}\n')

    def test_removal_allows_declared_lake_dependency(self):
        (self.tree / ".gitignore").write_text(".lake/\n")
        boundary = self.lake_dependency(self.tree, "mathlib")
        self.declare_lake_package(self.tree, "mathlib")
        (boundary / "unique").write_text("lake dependency bytes\n")
        result = self.remove()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse(self.tree.exists())

    def test_removal_refuses_undeclared_lake_dependency(self):
        boundary = self.lake_dependency(self.tree, "mathlib")
        self.declare_lake_package(self.tree, "other")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_lake_dependency_without_manifest(self):
        boundary = self.lake_dependency(self.tree, "mathlib")
        (self.tree / "lake-manifest.json").unlink()
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_malformed_lake_manifest(self):
        boundary = self.lake_dependency(self.tree, "mathlib")
        (self.tree / "lake-manifest.json").write_text("{\n")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_nonpackage_lake_nested_repository(self):
        boundary = self.tree / ".lake/other/x"
        boundary.mkdir(parents=True)
        self.g(boundary, "init")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_nested_repository_outside_lake_packages(self):
        boundary = self.tree / "ordinary/subtree"
        boundary.mkdir(parents=True)
        self.g(boundary, "init")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_allows_declared_nested_lake_project_dependency(self):
        (self.tree / ".gitignore").write_text(".lake/\n")
        project = self.tree / "tools/sub"
        project.mkdir(parents=True)
        boundary = self.lake_dependency(project, "pkg")
        self.declare_lake_package(project, "pkg")
        (boundary / "unique").write_text("nested lake dependency bytes\n")
        result = self.remove()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse(self.tree.exists())
