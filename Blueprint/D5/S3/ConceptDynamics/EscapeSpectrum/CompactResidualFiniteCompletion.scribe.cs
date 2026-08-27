using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class CompactResidualFiniteCompletionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion."
            + "compact_residual_finite_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact open separation of a residual space is witnessed by a finite "
            + "zero-spectrum budget.",
        H("Compact Residual Finite Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-residual-finite-completion"),
            DeclarationHandle.Create(Declaration),
            H("Compact residual separation has a finite zero-spectrum settlement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The residual E is the canonical defectRelation of the baseline "
                        + "readout q against the target T. For each active definition, "
                        + "its cut U is represented as an open subset of the subtype E, "
                        + "so the openness premise is exactly relative openness.")),
                Paragraph(Text(
                    "Blind-kernel emptiness invokes the existing finite_cover_laws "
                        + "equivalence to obtain a cover of E. Compactness then extracts "
                        + "a Finset S of the active-definition subtype Gamma.")),
                Paragraph(Text(
                    "Nonnegative candidate costs make the exact sum C(S) an NNReal "
                        + "budget L. The selected supplement has empty target defect, so "
                        + "its residual mass is zero and the canonical finiteEscapeSpectrum "
                        + "at L is zero.")),
                Paragraph(Text(
                    "No continuity of the definitions, analytic compactness, positive "
                        + "baseline mass, optimizer, or infimum-attainment claim is used."))),
            DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula baseType = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula valueFamily = F.Id("V");
        Formula gamma = Gamma;
        Formula definitions = F.Id("d");
        Formula baseReadout = F.Id("q");
        Formula target = F.Id("T");
        Formula cost = F.Id("c");
        Formula weight = Nu;
        Formula residual = F.Id("E");
        Formula definition = F.Id("a");
        Formula selection = F.Id("S");
        Formula budget = F.Id("L");
        Formula pair = F.Id("e");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nonnegativeReal = Sub(real, Seq(Geq, D(0)));
        Formula productStates = Seq(stateType, Sp, Times, Sp, stateType);
        Formula restrictedDefinitions = Seq(
            Open, definitions, Underscore, Grp(F.Id("i")), Close,
            Underscore, Grp(Seq(F.Id("i"), Sp, InMacro, Sp, gamma)));
        Formula kernel = Sub(F.Id("K"), definition);
        Formula cut = Sub(F.Id("U"), definition);
        Formula residualDefinition = Call(
            "defectRelation", baseReadout, target);
        Formula kernelDefinition = Call(
            "conceptKernel", restrictedDefinitions, definition);
        Formula cutDefinition = Seq(
            OpenBrace, pair, Colon, Sp, residual, Sp, Mid, Sp,
            Neg, Open, pair, Sp, InMacro, Sp, kernel, Close, CloseBrace);
        Formula blindKernel = Call(
            "intersection",
            residual,
            Call("jointKernel", restrictedDefinitions));
        Formula selectedResidual = Call(
            "defectRelation",
            Call(
                "conceptJoin",
                baseReadout,
                Call(
                    "finiteSelectionSupplement",
                    gamma,
                    definitions,
                    selection)),
            target);
        Formula selectedCost = Call(
            "finiteSelectionCost", gamma, cost, selection);
        Formula selectedSpectrum = Call(
            "finiteEscapeSpectrum",
            gamma,
            definitions,
            baseReadout,
            target,
            cost,
            weight,
            budget);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                baseType, Comma, Sp, targetType, Colon, Sp, type, Comma),
            Seq(
                valueFamily, Colon, Sp, indexType, Sp, To, Sp, type, Comma, Sp,
                gamma, Colon, Sp, Call("Set", indexType), Comma),
            Seq(
                Grp(), OpenBracket, Call("TopologicalSpace", productStates),
                CloseBracket, Comma),
            Seq(
                definitions, Colon, Sp, Forall, Sp, F.Id("i"), Colon, Sp,
                indexType, Comma, Sp, Call(
                    "Concept", stateType, Call("V", F.Id("i"))), Comma),
            Seq(
                baseReadout, Colon, Sp, Call("Concept", stateType, baseType),
                Comma, Sp,
                target, Colon, Sp, Call("Concept", stateType, targetType), Comma),
            Seq(
                cost, Colon, Sp, indexType, Sp, To, Sp, real, Comma, Sp,
                weight, Colon, Sp, Call("EscapeWeight", productStates), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                residual, Sp, Eq, Sp, residualDefinition, Comma, Sp,
                kernel, Sp, Eq, Sp, kernelDefinition, Comma),
            Seq(
                cut, Sp, Eq, Sp, cutDefinition, Comma),
            Seq(
                Call("IsCompact", residual), Sp, Land),
            Seq(
                blindKernel, Sp, Eq, Sp, Emptyset, Sp, Land),
            Seq(
                Open, Forall, Sp, definition, Sp, InMacro, Sp, gamma, Comma, Sp,
                Call("IsOpen", cut), Close, Sp, Land),
            Seq(
                Open, Forall, Sp, F.Id("i"), Sp, InMacro, Sp, gamma, Comma, Sp,
                D(0), Sp, Leq, Sp, Call("c", F.Id("i")), Close, Sp,
                Rightarrow),
            Seq(
                Exists, Sp, selection, Colon, Sp, Call("Finset", gamma),
                Comma, Sp, budget, Colon, Sp, nonnegativeReal, Comma),
            Seq(
                budget, Sp, Eq, Sp, selectedCost, Sp, Land),
            Seq(
                selectedResidual, Sp, Eq, Sp, Emptyset, Sp, Land),
            Seq(
                selectedSpectrum, Sp, Eq, Sp, D(0), Dot),
        ]));
    }
}
