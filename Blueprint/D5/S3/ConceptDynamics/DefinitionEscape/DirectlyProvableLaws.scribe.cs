using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class DirectlyProvableLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine direct DECT laws are packaged in an append-only dependent-family module.",
        H("Directly Provable DECT Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("directly-provable-dect-laws"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws."
                        + "directly_provable_laws"),
                H("Nine direct laws for definition escape and completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The nine conjuncts follow the source order exactly: residual "
                            + "intersection; sufficiency-factorization; zero gain from a "
                            + "redundant definition; blind-kernel impossibility; finite-object "
                            + "compactness; submodular capture; the prepared one-step defect "
                            + "identity; the semigroup defect identity; and the approximate "
                            + "cascade triangle bound.")),
                    Paragraph(Text(
                        "The first conjunct applies residual_join_law. The second uses the same "
                            + "fiber-constancy equivalence packaged by target_recovery_criterion, "
                            + "including the empty-state case without adding an inhabitedness "
                            + "premise. The fourth uses the new dependent-family obstruction; "
                            + "its residual witness supplies the inhabited state needed by the "
                            + "canonical recovery criterion.")),
                    Paragraph(Text(
                        "The canonical defectRelation is the only target residual throughout. "
                            + "Clauses four and five use dependentBlindResidual and "
                            + "dependentLanguageExtension because package members may have "
                            + "different codomains. On a constant codomain these are "
                            + "definitionally equal to the frozen blindResidual and "
                            + "languageExtension, as proved by the three specialization bridge "
                            + "theorems. The existing jointKernel and jointReadout remain the "
                            + "family primitives. For finite X, each baseline defect pair is "
                            + "assigned a package "
                            + "definition that separates it; enumeration of the finite subtype "
                            + "then gives a finite sufficient extension.")),
                    Paragraph(Text(
                        "CAS section 1.2 lets nu be a weight, count, or measure, and section 4.4 "
                            + "asserts submodularity for the resulting capture function. The "
                            + "sixth conjunct therefore quantifies over CaptureWeight, the "
                            + "existing EscapeWeight plus the single union-and-lower-intersection "
                            + "law used by the proof. Compiled constructors realize real-valued "
                            + "Set.ncard, a nontrivial point weight, and ENNReal.toReal of a finite "
                            + "measure, so no branch is selected by the packaged theorem. The "
                            + "seventh conjunct is the "
                            + "displayed "
                            + "composition identity, the eighth applies the general additive-time "
                            + "semigroup law, and the ninth instantiates the repository theorem "
                            + "naturality_defect_comp_le.")),
                    Paragraph(Text(
                        "Boolean examples witness a nonempty residual, redundant zero gain, a "
                            + "blind obstruction, and finite closure by one identity definition. "
                            + "A positive point weight gives a strict capture inequality. "
                            + "Coordinate "
                            + "swap on real pairs gives nonzero prepared and semigroup defects, "
                            + "and the real identity map attains the cascade bound. Nine named "
                            + "false-neighbor declarations compile concrete counterexamples to "
                            + "nearby strengthened or premise-weakened statements."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula baselineType = F.Id("C");
        Formula definitionType = F.Id("D");
        Formula targetType = F.Id("Target");
        Formula metricType = F.Id("Z");
        Formula middleType = F.Id("Y");
        Formula timeType = F.Id("Time");
        Formula edgeType = F.Id("Edge");
        Formula codeType = F.Id("Gamma");
        Formula definitionIndex = F.Id("Definition");
        Formula type = F.Id("Type");
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula definition = F.Id("d");
        Formula definitions = F.Id("definitions");
        Formula codomain = F.Id("Dgamma");
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula y = F.Id("y");
        Formula point = F.Id("point");
        Formula code = F.Id("code");
        Formula codes = F.Id("codes");
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula deltaPackage = F.Id("Delta");
        Formula recover = F.Id("recover");
        Formula projection = F.Id("projection");
        Formula prepare = F.Id("prepare");
        Formula update = F.Id("update");
        Formula evolution = F.Id("evolution");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula direct = F.Id("direct");
        Formula k = F.Id("K");
        Formula delta = F.Id("delta");
        Formula eta = F.Id("eta");
        Formula t = F.Id("t");
        Formula s = F.Id("s");
        Formula m = F.Id("m");
        Formula residualSet = F.Id("residual");
        Formula cut = F.Id("cut");
        Formula nu = F.Id("nu");
        Formula subset = F.Id("S");
        Formula captured = F.Id("captured");
        Formula residual = Call("defectRelation", q, target);
        Formula joinedResidual = Call(
            "defectRelation", Call("conceptJoin", q, definition), target);

        Formula clause1Body = Seq(
            joinedResidual, Sp, Eq, Sp,
            Call("intersection", residual, Call("ker", definition)));
        Formula clause1 = Seq(
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            definitionType, Comma, Sp, targetType, Colon, Sp, type, Comma, Esc,
            q, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            definition, Colon, Sp, Call("Concept", state, definitionType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc,
            clause1Body);

        Formula clause2 = Seq(
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            targetType, Colon, Sp, type, Comma, Esc,
            q, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc,
            residual, Sp, Eq, Sp, Emptyset, Sp, Leftrightarrow, Sp,
            Call("FactorsThrough", target, q));

        Formula clause3 = Seq(
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            definitionType, Comma, Sp, targetType, Colon, Sp, type, Comma, Esc,
            q, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            definition, Colon, Sp, Call("Concept", state, definitionType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc,
            Call("Refines", definition, q), Sp, Rightarrow, Sp,
            joinedResidual, Sp, Eq, Sp, residual);

        Formula selectedDefinitions = Seq(
            Open, i, Sp, Mapsto, Sp, Call("apply", definitions, Call("apply", codes, i)),
            Close);
        Formula finiteValues = Call("Pi", Seq(
            i, Colon, Sp, Call("Fin", n), Comma, Sp,
            Call("apply", codomain, Call("apply", codes, i))));
        Formula finiteRecovery = Seq(
            Neg, Exists, Sp, recover, Colon, Sp,
            Arrow(Call("Prod", baselineType, finiteValues), targetType), Comma, Esc,
            target, Sp, Eq, Sp,
            Call("comp", recover,
                Call("dependentLanguageExtension", q, selectedDefinitions)));
        Formula arbitraryDefinitions = Seq(
            Open, code, Sp, Mapsto, Sp,
            Call("apply", definitions, Call("val", code)), Close);
        Formula arbitraryValues = Call("Pi", Seq(
            code, Colon, Sp, deltaPackage, Comma, Sp,
            Call("apply", codomain, Call("val", code))));
        Formula arbitraryRecovery = Seq(
            Neg, Exists, Sp, recover, Colon, Sp,
            Arrow(Call("Prod", baselineType, arbitraryValues), targetType), Comma, Esc,
            target, Sp, Eq, Sp,
            Call("comp", recover,
                Call("dependentLanguageExtension", q, arbitraryDefinitions)));
        Formula dependentPackageBinders = Seq(
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            targetType, Comma, Sp, codeType, Colon, Sp, type, Comma, Esc,
            codomain, Colon, Sp, Arrow(codeType, type), Comma, Sp,
            definitions, Colon, Sp, Call("Pi", Seq(
                code, Colon, Sp, codeType, Comma, Sp,
                Call("Concept", state, Call("apply", codomain, code)))), Comma, Sp,
            q, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc);
        Formula clause4 = Seq(
            dependentPackageBinders,
            Call("Nonempty",
                Call("dependentBlindResidual", definitions, q, target)), Sp,
            Rightarrow, Sp, Open,
            Open, Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            codes, Colon, Sp, Arrow(Call("Fin", n), codeType), Comma, Esc,
            finiteRecovery, Close, Sp, Land, Sp,
            Open, Forall, Sp, deltaPackage, Colon, Sp, Call("Set", codeType),
            Comma, Esc, arbitraryRecovery, Close, Sp, Land, Sp,
            Neg, Call("dependentFiniteSelectionSufficient",
                definitions, q, target), Close);

        Formula clause5 = Seq(
            dependentPackageBinders,
            Open, Call("Finite", state), Sp, Land, Sp,
            Call("dependentBlindResidual", definitions, q, target), Sp, Eq, Sp,
            Emptyset, Close, Sp, Rightarrow, Sp,
            Exists, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            codes, Colon, Sp, Arrow(Call("Fin", n), codeType), Comma, Esc,
            Call("defectRelation",
                Call("dependentLanguageExtension", q, selectedDefinitions), target),
            Sp, Eq, Sp, Emptyset);

        Formula capturedDefinition = Seq(
            Call("apply", captured, subset), Sp, Eq, Sp,
            Call("intersection", residualSet,
                Call("iUnion", Seq(definition, Sp, InMacro, Sp, subset),
                    Call("apply", cut, definition))));
        Formula captureInequality = Seq(
            Call("mass", nu,
                Call("apply", captured, Call("union", a, b))), Sp, Plus, Sp,
            Call("mass", nu,
                Call("apply", captured, Call("intersection", a, b))), Sp,
            Leq, Sp,
            Call("mass", nu, Call("apply", captured, a)), Sp, Plus, Sp,
            Call("mass", nu, Call("apply", captured, b)));
        Formula clause6 = Seq(
            Forall, Sp, edgeType, Comma, Sp, definitionIndex, Colon, Sp,
            type, Comma, Esc,
            nu, Colon, Sp, Call("CaptureWeight", edgeType), Comma, Sp,
            residualSet, Colon, Sp, Call("Set", edgeType), Comma, Sp,
            cut, Colon, Sp, Arrow(definitionIndex, Call("Set", edgeType)), Comma, Sp,
            a, Comma, Sp, b, Colon, Sp, Call("Set", definitionIndex), Comma, Esc,
            captureInequality, Comma, Quad, Sp,
            F.Text, Grp(F.Id("where")), Sp,
            capturedDefinition);

        Formula projectedUpdatedPoint =
            Call("apply", projection, Call("apply", update, point));
        Formula preparedOneStep = Call("apply",
            Call("comp", projection, update, prepare),
            Call("apply", projection, point));
        Formula preparedPointOneStep = Call("apply", projection,
            Call("apply", update,
                Call("apply", Call("comp", prepare, projection), point)));
        Formula preparedEquality = Seq(
            Call("dist", projectedUpdatedPoint, preparedOneStep), Sp, Eq, Sp,
            Call("dist", projectedUpdatedPoint, preparedPointOneStep));
        Formula clause7 = Seq(
            Forall, Sp, state, Comma, Sp, metricType, Colon, Sp, type,
            Comma, Esc,
            OpenBracket, Call("PseudoMetricSpace", metricType), CloseBracket,
            Comma, Sp,
            projection, Colon, Sp, Arrow(state, metricType), Comma, Sp,
            update, Colon, Sp, Arrow(state, state), Comma, Sp,
            prepare, Colon, Sp, Arrow(metricType, state), Comma, Sp,
            point, Colon, Sp, state, Comma, Esc,
            Call("RightInverse", prepare, projection), Sp, Rightarrow, Sp,
            preparedEquality);

        Formula preparedM = Call("apply", prepare, m);
        Formula evolvedS = Call("apply", evolution, s, preparedM);
        Formula evolvedTAfterS = Call("apply", evolution, t, evolvedS);
        Formula rePreparedS = Call("apply", prepare,
            Call("apply", projection, evolvedS));
        Formula evolvedTAfterReprepare = Call("apply", evolution, t, rePreparedS);
        Formula semigroupEquality = Seq(
            Call("dist",
                Call("apply", projection,
                    Call("apply", evolution, Seq(t, Sp, Plus, Sp, s), preparedM)),
                Call("apply", projection, evolvedTAfterReprepare)),
            Sp, Eq, Sp,
            Call("dist", Call("apply", projection, evolvedTAfterS),
                Call("apply", projection,
                    Call("apply", evolution, t,
                        Call("apply", Call("comp", prepare, projection), evolvedS)))));
        Formula semigroupLaw = Seq(
            Forall, Sp, t, Comma, Sp, s, Colon, Sp, timeType, Comma, Sp,
            point, Colon, Sp, state, Comma, Esc,
            Call("apply", evolution, Seq(t, Sp, Plus, Sp, s), point),
            Sp, Eq, Sp,
            Call("apply", evolution, t,
                Call("apply", evolution, s, point)));
        Formula clause8 = Seq(
            Forall, Sp, state, Comma, Sp, metricType, Comma, Sp,
            timeType, Colon, Sp, type, Comma, Esc,
            OpenBracket, Call("PseudoMetricSpace", metricType), CloseBracket,
            Comma, Sp, OpenBracket, Call("Add", timeType), CloseBracket,
            Comma, Sp,
            projection, Colon, Sp, Arrow(state, metricType), Comma, Sp,
            evolution, Colon, Sp, Arrow(timeType, Arrow(state, state)), Comma, Sp,
            prepare, Colon, Sp, Arrow(metricType, state), Comma, Sp,
            t, Comma, Sp, s, Colon, Sp, timeType, Comma, Sp,
            m, Colon, Sp, metricType, Comma, Esc,
            Open, Call("RightInverse", prepare, projection), Sp, Land, Sp,
            semigroupLaw, Close, Sp, Rightarrow, Sp,
            semigroupEquality);

        Formula clause9 = Seq(
            Forall, Sp, state, Comma, Sp, middleType, Comma, Sp,
            metricType, Colon, Sp, type, Comma, Esc,
            OpenBracket, Call("PseudoMetricSpace", middleType), CloseBracket,
            Comma, Sp, OpenBracket, Call("PseudoMetricSpace", metricType),
            CloseBracket, Comma, Sp,
            first, Colon, Sp, Arrow(state, middleType), Comma, Sp,
            second, Colon, Sp, Arrow(middleType, metricType), Comma, Sp,
            direct, Colon, Sp, Arrow(state, metricType), Comma, Sp,
            k, Colon, Sp, F.Id("NNReal"), Comma, Sp,
            delta, Comma, Sp, eta, Colon, Sp, F.Id("Real"), Comma, Sp,
            point, Colon, Sp, state, Comma, Sp, y, Colon, Sp, middleType,
            Comma, Esc,
            Open, Call("LipschitzWith", k, second), Sp, Land, Sp,
            Call("dist", Call("apply", first, point), y), Sp, Leq, Sp,
            delta, Sp, Land, Sp,
            Call("dist", Call("apply", second, y),
                Call("apply", direct, point)), Sp, Leq, Sp,
            eta, Close, Sp, Rightarrow, Sp,
            Call("dist", Call("apply", second, Call("apply", first, point)),
                Call("apply", direct, point)),
            Sp, Leq, Sp, k, Sp, Times, Sp, delta, Sp, Plus, Sp, eta);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, clause1, Close, Sp, Land, RowBreak,
            Open, clause2, Close, Sp, Land, RowBreak,
            Open, clause3, Close, Sp, Land, RowBreak,
            Open, clause4, Close, Sp, Land, RowBreak,
            Open, clause5, Close, Sp, Land, RowBreak,
            Open, clause6, Close, Sp, Land, RowBreak,
            Open, clause7, Close, Sp, Land, RowBreak,
            Open, clause8, Close, Sp, Land, RowBreak,
            Open, clause9, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
