import unittest

from pathlib import Path
from unittest.mock import patch

from report import check_coverage, verify_complete


def site(owner, name, **attributes):
    return {"originalTypeChecked": attributes.get("matchingNameAndModule", False), "module": owner, "name": name, "kind": "theorem", "matchingNameAndModule": False,
            "unsafe": False, "partial": False, "strictUnsafe": False, "strictPartial": False,
            "strictModule": None, "impliesAxiom": None, "reductionWitness": None, **attributes}


def inventory(*rows):
    return {"modules": sorted({row["module"] for row in rows}), "declarations": rows,
            "summary": {"declarations": len(rows), "directAxioms": sum(r["kind"] == "axiom" for r in rows),
                        "matchingNameAndModule": sum(r["matchingNameAndModule"] for r in rows)}}


class CoverageTest(unittest.TestCase):
    def test_completion_checks_safety_and_partiality_at_matching_sites(self):
        for flags in ({"unsafe": True}, {"strictUnsafe": True}, {"partial": True}, {"strictPartial": None}):
            with self.subTest(flags=flags):
                data = inventory(site("Init.Core", "f", matchingNameAndModule=True, strictModule="OmegaInit.Core", **flags))
                with self.assertRaisesRegex(ValueError, "1 matched definitions differ in safety or partiality"):
                    verify_complete(data, Path("product"), *check_coverage(data))

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

    def test_unsafe_cast_requires_its_pinned_kernel_reduction(self):
        cast = site("Init.Prelude", "unsafeCast", kind="definition", unsafe=True,
                    impliesAxiom="sorryAx", reductionWitness="sorryAxFromUnsafeCast")
        with self.assertRaisesRegex(ValueError, "invalid pinned reduction"):
            check_coverage(inventory(cast))
        self.assertEqual(check_coverage(inventory({**cast, "kernelReductionAxiom": "lcProof"})),
                         (0, [("Init.Prelude", "unsafeCast")]))

    def test_safe_reduction_leaves_an_unsafe_declaration_open(self):
        cast = site("Init.Prelude", "testUnsafe", kind="definition", unsafe=True,
                    impliesAxiom="sorryAx", reductionWitness="sorryAxFromSafeImplementation")
        take = site("Init.System.ST", "ST.Prim.Ref.take", kind="opaque", unsafe=True,
                    strictImpliesAxiom="Classical.choice.{1}",
                    strictSelectionWitness="OmegaStrictReference.ST.Prim.Ref.take")
        reductions, open_sites = check_coverage(inventory(cast, take))
        self.assertEqual(reductions, 0)
        self.assertEqual(open_sites, [(r["module"], r["name"]) for r in (cast, take)])

    def test_runtime_conflict_requires_live_observation_and_matching_contradiction(self):
        attributes = dict(kind="opaque", unsafe=True, logicalConsequence="False",
                          logicalConsequenceWitness="address", requiredBehavior="distinguish equal lists")
        observed = site("Init.Util", "ptrAddrUnsafe", runtimeConflictWitness="address", **attributes)
        conditional = site("Init.Util", "ptrEq", **attributes)
        self.assertEqual(check_coverage(inventory(observed, conditional)),
                         (0, [("Init.Util", "ptrAddrUnsafe"), ("Init.Util", "ptrEq")]))
        with self.assertRaisesRegex(ValueError, "2 unresolved"):
            data = inventory(observed, conditional)
            verify_complete(data, Path("product"), *check_coverage(data))
        for mismatch in ({"logicalConsequence": "funext"}, {"logicalConsequenceWitness": "other"},
                         {"requiredBehavior": None}, {"unsafe": False}, {"kind": "axiom"}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "runtime conflict"):
                check_coverage(inventory({**observed, **mismatch}))

    def test_verified_specialization_still_requires_the_original_type(self):
        row = site("Init.Data.Erased", "Erased.out_mk", matchingNameAndModule=True,
                   strictModule="OmegaInit.Data.Erased", originalTypeChecked=False,
                   originalTypeGap="missing type dependencies: Omega.Erased.out")
        data = inventory(row)
        data["schemaVersion"] = 5
        data["summary"]["originalTypesChecked"] = 0
        self.assertEqual(check_coverage(data), (0, [(row["module"], row["name"])]))
        with self.assertRaisesRegex(ValueError, "1 unresolved"):
            verify_complete(data, Path("product"), *check_coverage(data))

    def test_strict_excluded_middle_is_a_logical_consequence(self):
        row = site("Init.Data.String.Lemmas.Pattern.Basic", "String.Slice.Pattern.Model.IsMatch.exists_isLongestMatch",
                   logicalConsequence="Classical.em", strictLogicalConsequence="Classical.em",
                   strictLogicalConsequenceWitness="OmegaStrictString.excludedMiddleOfLongest")
        self.assertEqual(check_coverage(inventory(row)), (0, [(row["module"], row["name"])]))

    def test_matched_unsafe_observation_retains_the_pure_replacement_counterexample(self):
        row = site("Init.Util", "isExclusiveUnsafe", kind="opaque", unsafe=True,
                   matchingNameAndModule=True, strictModule="OmegaInit.Util",
                   checkedUnsafeRuntime="lean_is_exclusive_obj", runtimeConflictWitness="exclusivity",
                   logicalConsequence="False", logicalConsequenceWitness="exclusivity",
                   requiredBehavior="distinguish equal arrays")
        self.assertEqual(check_coverage(inventory(row)), (0, []))
        for mismatch in ({"checkedUnsafeRuntime": None}, {"checkedUnsafeRuntime": "other"},
                         {"name": "other"}, {"unsafe": False}, {"runtimeConflictWitness": None},
                         {"checkedUnsafeRuntime": None, "runtimeConflictWitness": None}):
            with self.subTest(mismatch=mismatch), self.assertRaises(ValueError):
                check_coverage(inventory(row | mismatch))

    def test_share_observers_require_their_own_runtime_symbol(self):
        for member in ("eq", "hash"):
            row = site("Init.ShareCommon", f"ShareCommon.Object.{member}", kind="opaque", unsafe=True,
                       matchingNameAndModule=True, strictModule="OmegaInit.ShareCommon",
                       checkedUnsafeRuntime=f"lean_sharecommon_{member}")
            self.assertEqual(check_coverage(inventory(row)), (0, []))
            for change in ({"checkedUnsafeRuntime": None}, {"checkedUnsafeRuntime": "other"},
                           {"unsafe": False}, {"matchingNameAndModule": False}):
                with self.subTest(member=member, change=change), self.assertRaises(ValueError):
                    check_coverage(inventory(row | change))

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
        certificate = {"certifiedChoiceEndpoints": [("Init.While", row["name"], "Classical.choice", "fromChoice")]}
        self.assertEqual(check_coverage(inventory(row) | certificate), (0, []))
        fake = site("Init.ByCases", "ite.congr_simp", equationOperand="ite",
                    operandImpliesAxiom="Classical.choice", operandReductionWitness="doesNotExist",
                    specializedEndpointType="Classical.choice")
        with self.assertRaisesRegex(ValueError, "uncertified specialized equality endpoint"):
            check_coverage(inventory(row, fake) | certificate)
        for mismatch in ({"kind": "definition"}, {"equationOperand": "other"}, {"operandReductionWitness": None},
                         {"specializedEndpointType": "propext"}, {"matchingNameAndModule": True}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "equality endpoint"):
                check_coverage(inventory({**row, **mismatch}) | certificate)

    def test_selector_specification_certificates_must_identify_the_official_site_and_operand(self):
        def checked(owner, name, selector):
            row = site(owner, name, equationOperand=selector, operandImpliesAxiom="Classical.choice",
                       operandReductionWitness="checked", specializedEndpointType="Classical.choice")
            certificate = {"certifiedChoiceEndpoints": [(owner, name, selector, "checked")]}
            return check_coverage(inventory(row) | certificate)

        for name, selector in [("Classical.choose_spec", "Classical.choose"), ("Exists.choose_spec", "Exists.choose"),
                               ("Classical.epsilon_spec", "Classical.epsilon"),
                               ("Classical.epsilon_spec_aux", "Classical.epsilon")]:
            self.assertEqual(checked("Init.Classical", name, selector), (0, []))
            for owner, decl, operand in [("Init.ByCases", name, selector),
                                         ("Init.Classical", "Unrelated.fake_spec", selector),
                                         ("Init.Classical", name, "unknownSelector")]:
                with self.subTest(decl=decl, owner=owner, operand=operand), self.assertRaisesRegex(
                        ValueError, "inconsistent specialized equality endpoint"):
                    checked(owner, decl, operand)

    def test_quotient_statement_formation_requires_an_independent_argument_certificate(self):
        row = site("Init.Core", "Quot.liftIndepPr1", logicalConsequence="Quot.sound",
                   logicalConsequenceWitness="soundOfLiftArgument", requiredBehavior="supply pair coherence")
        site_key = (row["module"], row["name"])
        self.assertEqual(check_coverage(inventory(row)), (0, [site_key]))
        arg = "Quot.indepCoherent"
        certificate = {"certifiedFormationArguments": [[*site_key, arg, "Quot.sound", "soundOfLiftArgument"]]}
        row["formationArgument"] = arg
        self.assertEqual(check_coverage(inventory(row) | certificate), (0, []))
        with self.assertRaisesRegex(ValueError, "uncertified statement formation argument"):
            check_coverage(inventory(row))
        for mismatch in ({"logicalConsequenceWitness": "other"}, {"kind": "definition"},
                         {"matchingNameAndModule": True}):
            with self.subTest(mismatch=mismatch), self.assertRaisesRegex(ValueError, "statement formation argument"):
                check_coverage(inventory(row | mismatch) | certificate)

    def test_loop_unfolding_requires_the_complete_endpoint_and_its_behavior(self):
        owner = "Init.Internal.Order.While"
        name = "Lean.Loop.forIn.eq_1"
        op = "Lean.Loop.forIn"
        proof = "OmegaChecks.InitBoundaries.WhileChoice.choiceFromLoop"
        row = site(owner, name, formationArgument=op, logicalConsequence="Classical.choice",
                   logicalConsequenceWitness=proof, requiredBehavior="the pinned fixed-point observation")
        cert = {"certifiedFormationArguments": [[owner, name, op, "Classical.choice", proof]]}
        self.assertEqual(check_coverage(inventory(row) | cert), (0, []))
        for change in ({"name": "Lean.Loop.forIn_eq_of_monadTail"}, {"formationArgument": "repeatM"},
                       {"requiredBehavior": None}, {"unsafe": True}):
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, "statement formation argument"):
                check_coverage(inventory(row | change) | cert)

    def test_setoid_transport_path_requires_its_representative_counterexample(self):
        for carrier in ("Quot", "Quotient"):
            for recursor in (".rec", ".recOn"):
                row = site("Init.Core", carrier + recursor, kind="definition", transportPathType=carrier + ".sound")
                site_key = (row["module"], row["name"])
                certificate = {"certifiedTransportPaths": [[*site_key, row["transportPathType"]]]}
                expected = [site_key] if carrier == "Quotient" else []
                self.assertEqual(check_coverage(inventory(row) | certificate), (0, expected))
                with self.assertRaisesRegex(ValueError, "uncertified transport path"):
                    check_coverage(inventory(row))
                with self.assertRaisesRegex(ValueError, "inconsistent transport path"):
                    check_coverage(inventory(row | {"kind": "theorem"}) | certificate)

    def test_envelope_cancellation_requires_the_pinned_owner_and_observed_declaration(self):
        proof = "OmegaChecks.InitBoundaries.RepresentativeQuotient.refuteEnvelopeCancellation"
        for owner, name, kind in [
                ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.neg_add_cancel", "theorem"),
                ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring.add.eq_1", "theorem"),
                ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule.ofNatModule", "definition")]:
            row = site(owner, name, kind=kind, representativeRefuter=proof)
            certificate = [[owner, name, name, proof]]
            self.assertEqual(check_coverage(dict(inventory(row), certifiedRepresentativeRefutations=certificate)), (0, []))
            for change in ({"module": "Init.Core"}, {"name": "another.operation"}, {"kind": "opaque"}):
                altered = {**row, **change}
                data = inventory(altered)
                data["certifiedRepresentativeRefutations"] = [[altered["module"], altered["name"], altered["name"], proof]]
                with self.assertRaisesRegex(ValueError, "inconsistent representative"):
                    check_coverage(data)

    def test_lift_coherence_keeps_the_operation_open(self):
        proof = "OmegaChecks.InitBoundaries.RepresentativeQuotient.refuteEnvelopeCancellation"
        for owner, prefix, ops in [
                ("Init.Grind.Ring.Envelope", "Lean.Grind.Ring.OfSemiring", ("add", "sub", "mul", "neg")),
                ("Init.Grind.Module.Envelope", "Lean.Grind.IntModule.OfNatModule", ("add", "sub", "neg"))]:
            for op in ops:
                name = f"{prefix}.{op}"
                row = site(owner, name, kind="definition", pinnedLiftCoherenceRefuter=proof)
                self.assertEqual(check_coverage(inventory(row)), (0, [(owner, name)]))
                data = inventory(row | {"representativeRefuter": proof})
                data["certifiedRepresentativeRefutations"] = [[owner, name, name, proof]]
                with self.assertRaisesRegex(ValueError, "inconsistent representative"):
                    check_coverage(data)

    def test_representative_quotient_models_are_bound_to_the_statement_or_certified_path(self):
        for name, target, suffix in [("Quotient.sound", "Quotient.sound", "refuteSound"),
                                     ("instSubsingletonSquash", "instSubsingletonSquash", "refuteSquash"),
                                     ("Quotient.rec", "Quotient.sound", "refuteSound"),
                                     ("Quotient.recOn", "Quotient.sound", "refuteSound")]:
            key = ["Init.Core", name]
            proof = "OmegaChecks.InitBoundaries.RepresentativeQuotient." + suffix
            row = site(*key, representativeRefuter=proof)
            certificates = {"certifiedRepresentativeRefutations": [[*key, target, proof]]}
            if name != target:
                row.update(kind="definition", transportPathType=target)
                certificates["certifiedTransportPaths"] = [[*key, target]]
            with self.subTest(name=name):
                self.assertEqual(check_coverage(inventory(row) | certificates), (0, []))
                with self.assertRaisesRegex(ValueError, "uncertified representative"):
                    check_coverage(inventory(row) | (certificates | {"certifiedRepresentativeRefutations": []}))
                with self.assertRaisesRegex(ValueError, "inconsistent representative"):
                    check_coverage(inventory(row) | (certificates |
                        {"certifiedRepresentativeRefutations": [[*key, "Quot.sound", proof]]}))
                with self.assertRaisesRegex(ValueError, "inconsistent representative"):
                    check_coverage(inventory(row | {"unsafe": True}) | certificates)
                if name != target:
                    with self.assertRaisesRegex(ValueError, "uncertified transport path"):
                        check_coverage(inventory(row) | (certificates | {"certifiedTransportPaths": []}))

    def test_quotient_decision_counterexample_requires_its_computation(self):
        name = "Quotient.decidableEq"
        proof = "OmegaChecks.InitBoundaries.RepresentativeQuotient.refutePositiveDecision"
        row = site("Init.Core", name, kind="definition", logicalConsequence="funext",
                   requiredBehavior="true on the distinct representatives", representativeRefuter=proof)
        certificate = {"certifiedRepresentativeRefutations": [["Init.Core", name, name, proof]]}
        self.assertEqual(check_coverage(inventory(row) | certificate), (0, []))
        plain = row.copy()
        del plain["representativeRefuter"]
        self.assertEqual(check_coverage(inventory(plain)), (0, [("Init.Core", name)]))
        for changed in ({"requiredBehavior": None}, {"kind": "theorem"}, {"logicalConsequence": "False"}):
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, "inconsistent representative"):
                check_coverage(inventory(row | changed) | certificate)

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
