"""Actions publication authority and measured-work contracts."""


class PublicationCases:
    def test_project_zero_report_and_program_work_skips_upload(self):
        self.native_seed("project")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("no-build-work", ready["project_skip_reason"])
        self.assertEqual("no-build-work", receipts["project"]["reason"])

    def test_explicit_release_seed_can_warm_protected_actions_cache_without_recompilation(self):
        self.native_seed("project")
        self.work(0, 0)
        self.env.update(GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_REF="refs/heads/dev",
                        STRATALINT_CACHE_SOURCE_VALIDATED="true", STRATALINT_CACHE_SOURCE_REF="refs/heads/dev",
                        STRATALINT_CACHE_SOURCE_COMMIT="a" * 40, STRATALINT_CACHE_CHECKED_OUT_SHA="a" * 40,
                        STRATALINT_RELEASE_CACHE_SEEDED="1")
        ready, receipts = self.snapshot_result()
        self.assertEqual("true", ready["project_ready"])
        self.assertEqual(0, receipts["project"]["build_work"])
        for defect in ({"STRATALINT_RELEASE_CACHE_SEEDED": "0"}, {"STRATALINT_REPORT_SUCCEEDED": "false"},
                       {"STRATALINT_CACHE_SOURCE_VALIDATED": "false"}, {"GITHUB_EVENT_NAME": "pull_request"}):
            with self.subTest(defect=defect):
                valid = self.env.copy()
                self.env.update(defect)
                ready, _ = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.env = valid

    def test_project_report_and_program_only_work_are_publishable_on_push(self):
        self.native_seed("project")
        for report, programs in ((2, 0), (0, 3)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("true", ready["project_ready"])
                self.assertEqual(report + programs, receipts["project"]["build_work"])

    def test_project_unknown_work_never_claims_zero_or_uploads(self):
        self.native_seed("project")
        for defect in ("missing", "malformed", "stale", "negative", "bool", "unknown", "foreign-root", "duplicate-field", "archived-path", "symlink"):
            with self.subTest(defect=defect):
                path = self.work()
                if defect == "missing": path.unlink()
                elif defect == "malformed": path.write_text("[]")
                elif defect == "stale": self.work(run_attempt="1")
                elif defect == "negative": self.work(-1)
                elif defect == "bool": self.work(True)
                elif defect == "unknown": self.work(None)
                elif defect == "foreign-root": self.work(repository="/other")
                elif defect == "duplicate-field": path.write_text(path.read_text().rstrip()[:-1] + ', "report": 0}')
                elif defect == "archived-path":
                    archived = self.root / ".lake/build/work.json"
                    archived.write_bytes(path.read_bytes())
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(archived)
                elif defect == "symlink":
                    link = path.with_suffix(".link")
                    link.symlink_to(path)
                    self.env["STRATALINT_LEAN_BUILD_WORK_FILE"] = str(link)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("build-work-unknown", ready["project_skip_reason"])
                self.assertEqual("build-work-unknown", receipts["project"]["reason"])

    def test_project_work_from_another_run_cannot_publish(self):
        self.native_seed("project")
        self.work(run_id="16")
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("build-work-unknown", receipts["project"]["reason"])

    def test_ordinary_pull_requests_never_publish_project_seeds_even_with_build_work(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.env.update(GITHUB_EVENT_NAME="pull_request", GITHUB_REF="refs/pull/12/merge")
        for report, programs in ((2, 0), (0, 3), (0, 0), (None, None)):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])
                self.assertEqual("pull-requests-do-not-publish-project-seeds", receipts["project"]["reason"])
                self.assertEqual("true", ready["dependency_ready"])

    def test_pr_dispatch_never_publishes_candidate_to_ordinary_native_prefix(self):
        _, _, target = self.native_seed("project")
        self.env.update(GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_REF="refs/heads/dev",
                        STRATALINT_CACHE_PR_SOURCE_VALIDATED="true", STRATALINT_CACHE_SOURCE_REF="refs/pull/12/merge",
                        STRATALINT_CACHE_TARGET_REF="refs/heads/dev",
                        STRATALINT_CACHE_SOURCE_COMMIT="a" * 40, STRATALINT_CACHE_CHECKED_OUT_SHA="a" * 40)
        for report, programs, expected in ((2, 0, "false"), (0, 3, "false"), (0, 0, "false"), (None, None, "false")):
            with self.subTest(report=report, programs=programs):
                self.work(report, programs)
                ready, receipts = self.snapshot_result()
                self.assertEqual(expected, ready["project_ready"])
                if expected == "true":
                    self.assertEqual(report + programs, receipts["project"]["build_work"])
                self.assertEqual(b"native build material", (target / "module.olean").read_bytes())

    def test_pr_dispatch_publication_rejects_missing_authorization_or_wrong_source_scope(self):
        self.native_seed("project")
        self.work(2, 0)
        valid = dict(self.env, GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_REF="refs/heads/dev",
                     STRATALINT_CACHE_PR_SOURCE_VALIDATED="true", STRATALINT_CACHE_SOURCE_REF="refs/pull/12/merge",
                     STRATALINT_CACHE_TARGET_REF="refs/heads/dev", STRATALINT_CACHE_SOURCE_COMMIT="a" * 40,
                     STRATALINT_CACHE_CHECKED_OUT_SHA="a" * 40)
        for defect in ({"STRATALINT_CACHE_PR_SOURCE_VALIDATED": "false"},
                       {"STRATALINT_CACHE_WRITES": "false"}, {"STRATALINT_REPORT_SUCCEEDED": "false"},
                       {"GITHUB_REF": "refs/heads/integration-another"}, {"STRATALINT_CACHE_SOURCE_REF": "refs/pull/12/head"},
                       {"STRATALINT_CACHE_SOURCE_REF": "refs/pull/0/merge"}, {"STRATALINT_CACHE_CHECKED_OUT_SHA": "b" * 40},
                       {"STRATALINT_CACHE_SOURCE_COMMIT": "0" * 40}, {"GITHUB_EVENT_NAME": "pull_request"}):
            with self.subTest(defect=defect):
                self.env = dict(valid, **defect)
                ready, _ = self.snapshot_result()
                self.assertEqual("false", ready["project_ready"])

    def test_only_dev_and_integration_pushes_publish_project_seeds(self):
        self.native_seed("project")
        for ref, expected in (("refs/heads/dev", "true"),
                ("refs/heads/integration-ci-perf-tests", "true"), ("refs/heads/topic", "false")):
            with self.subTest(ref=ref):
                self.env["GITHUB_REF"] = ref
                ready, _ = self.snapshot_result()
                self.assertEqual(expected, ready["project_ready"])

    def test_project_save_authorization_and_dependency_policy_remain_independent(self):
        self.native_seed("project")
        self.native_seed("dependency")
        self.work(0, 0)
        ready, receipts = self.snapshot_result()
        self.assertEqual("true", ready["dependency_ready"])
        self.env["STRATALINT_CACHE_WRITES"] = "false"
        ready, receipts = self.snapshot_result()
        self.assertEqual("false", ready["project_ready"])
        self.assertEqual("false", ready["dependency_ready"])
        self.assertEqual("save-disabled", receipts["project"]["status"])

    def test_project_guard_requires_report_success_and_dependency_requires_check_success(self):
        self.native_seed("project")
        self.native_seed("dependency")
        for report, checked, project, dependency in (("true", "false", "true", "false"),
                ("false", "true", "false", "true"), (None, "true", "false", "true"), ("true", "true", "true", "true")):
            with self.subTest(report=report, checked=checked):
                self.env["STRATALINT_CHECK_SUCCEEDED"] = checked
                self.env.pop("STRATALINT_REPORT_SUCCEEDED", None)
                if report is not None: self.env["STRATALINT_REPORT_SUCCEEDED"] = report
                ready, _ = self.snapshot_result()
                self.assertEqual(project, ready["project_ready"])
                self.assertEqual(dependency, ready["dependency_ready"])
