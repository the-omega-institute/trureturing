import unittest

from pathlib import Path
from unittest.mock import patch

from report import check_coverage, verify_complete


def site(owner, name, **attributes):
    return {"module": owner, "name": name, "kind": "theorem", "matchingNameAndModule": False,
            "strictModule": None, "impliesAxiom": None, "reductionWitness": None, **attributes}


def inventory(*rows):
    return {"modules": sorted({row["module"] for row in rows}), "declarations": rows,
            "summary": {"declarations": len(rows), "directAxioms": sum(r["kind"] == "axiom" for r in rows),
                        "matchingNameAndModule": sum(r["matchingNameAndModule"] for r in rows)}}


class CoverageTest(unittest.TestCase):
    def test_same_name_other_owner_and_implementation_axioms_leave_a_gap(self):
        data = inventory(
            site("Init.A", "a", kind="axiom"),
            site("Init.A", "t", matchingNameAndModule=True, strictModule="OmegaInit.A"),
            site("Init.B", "t", axioms=["propext"]),
            site("Init.C", "t", impliesAxiom="propext", reductionWitness="SomeProof"),
            site("Init.D", "q", kind="quotientPrimitive"),
        )
        self.assertEqual(check_coverage(data), (1, [("Init.B", "t"), ("Init.D", "q")]))

    def test_completion_rejects_unresolved_even_with_old_audit_receipts(self):
        data = inventory(site("Init.Core", "open", axioms=["Classical.choice"]))
        with patch("report.subprocess.run") as audit:
            with self.assertRaisesRegex(ValueError, "1 unresolved"):
                verify_complete(data, Path("old-product"), *check_coverage(data))
            audit.assert_not_called()

    def test_completed_coverage_runs_live_interface_and_kernel_checks(self):
        data = inventory(site("Init.Core", "found", matchingNameAndModule=True, strictModule="OmegaInit.Core"),
                         site("Init.Extra", "boundary", impliesAxiom="propext", reductionWitness="proof"))
        with patch("report.subprocess.run") as run:
            verify_complete(data, Path("product"), *check_coverage(data))
            commands = [call.args[0] for call in run.call_args_list]
            axiom_check, = [command for command in commands if "--check" in command]
            self.assertIn("OmegaInit.Extra", axiom_check)
            self.assertIn("--exact-roots", commands[-1])
            self.assertTrue(all(call.kwargs["check"] for call in run.call_args_list))

    def test_matched_definition_requires_its_official_native_signature(self):
        row = site("Init.Core", "found", kind="definition", matchingNameAndModule=True,
                   strictModule="OmegaInit.Core", strictNativeSignature=False)
        boundary = site("Init.Core", "boundary", kind="opaque", strictNativeSignature=False,
                        impliesAxiom="Classical.choice", reductionWitness="proof")
        with patch("report.subprocess.run") as run:
            data = inventory(row, boundary)
            with self.assertRaisesRegex(ValueError, "1 matched definitions.*Init.Core/found"):
                verify_complete(data, Path("product"), *check_coverage(data))
            run.assert_not_called()
            data = inventory({**row, "strictNativeSignature": True}, boundary)
            verify_complete(data, Path("product"), *check_coverage(data))
            self.assertTrue(run.called)

    def test_witness_required_for_each_claimed_reduction(self):
        with self.assertRaisesRegex(ValueError, "incomplete axiom reduction"):
            check_coverage(inventory(site("Init.Core", "t", impliesAxiom="propext")))

    def test_runtime_conflict_requires_live_observation_and_matching_contradiction(self):
        attributes = dict(kind="opaque", unsafe=True, logicalConsequence="False",
                          logicalConsequenceWitness="address", requiredBehavior="distinguish equal lists")
        observed = site("Init.Util", "ptrAddrUnsafe", runtimeConflictWitness="address", **attributes)
        conditional = site("Init.Util", "ptrEq", **attributes)
        self.assertEqual(check_coverage(inventory(observed, conditional)), (0, [("Init.Util", "ptrEq")]))
        for mismatch in ({"logicalConsequence": "funext"}, {"logicalConsequenceWitness": "other"},
                         {"requiredBehavior": None}, {"unsafe": False}, {"kind": "axiom"}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "runtime conflict"):
                check_coverage(inventory({**observed, **mismatch}))

    def test_unsafe_packing_alone_leaves_declared_input_unresolved(self):
        row = site("Init.ShareCommon", "ShareCommon.Object.eq", kind="opaque", unsafe=True,
                   logicalConsequence="False", logicalConsequenceWitness="packedPayloadEquality",
                   requiredBehavior="preserve native payloads under a pure packing of nested lists",
                   unsafePackedObservation="unsafeCast of equal nested lists produced different results")
        self.assertEqual(check_coverage(inventory(row)), (0, [("Init.ShareCommon", "ShareCommon.Object.eq")]))

    def test_equation_operand_does_not_resolve_the_equation(self):
        equation = site("Init.While", "Classical.choice.congr_simp", equationOperand="Classical.choice",
                        operandImpliesAxiom="Classical.choice", operandReductionWitness="fromChoice")
        self.assertEqual(check_coverage(inventory(equation)), (0, [("Init.While", "Classical.choice.congr_simp")]))

    def test_unrepresentable_statement_requires_choice_from_its_specialized_endpoints(self):
        row = site("Init.While", "Classical.choice.congr_simp", equationOperand="Classical.choice",
                   operandImpliesAxiom="Classical.choice", operandReductionWitness="fromChoice",
                   specializedEndpointType="Classical.choice")
        self.assertEqual(check_coverage(inventory(row)), (0, []))
        for mismatch in ({"kind": "definition"}, {"equationOperand": "other"}, {"operandReductionWitness": None},
                         {"specializedEndpointType": "propext"}, {"matchingNameAndModule": True}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "equality endpoint"):
                check_coverage(inventory({**row, **mismatch}))

    def test_strict_choice_requires_a_checked_target_and_an_unimplemented_site(self):
        row = site("Init.System.ST", "ST.Prim.Ref.get", strictImpliesAxiom="Classical.choice.{1}",
                   strictSelectionWitness="OmegaStrictReference.ST.Prim.Ref.get")
        self.assertEqual(check_coverage(inventory(row)), (1, []))
        for mismatch in ({"strictImpliesAxiom": None}, {"strictImpliesAxiom": "Classical.choice"},
                         {"strictSelectionWitness": "wrong"}, {"matchingNameAndModule": True}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "strict choice"):
                check_coverage(inventory({**row, **mismatch}))

    def test_refuse_duplicate_definition_site(self):
        with self.assertRaisesRegex(ValueError, "repeated official definition site"):
            check_coverage(inventory(site("Init.A", "t"), site("Init.A", "t")))

    def test_refuse_empty_or_truncated_denominator(self):
        with self.assertRaisesRegex(ValueError, "counts"):
            check_coverage(inventory())
        data = inventory(site("Init.A", "t"))
        data["summary"]["declarations"] += 1
        with self.assertRaisesRegex(ValueError, "counts"):
            check_coverage(data)


if __name__ == "__main__":
    unittest.main()
