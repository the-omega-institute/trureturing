using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class BlindResidualChargeDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition."
            + "blind_residual_charge_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite selected residual decomposes into its blind and "
            + "finitely removable charge.",
        H("Blind Residual Charge Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("blind-residual-charge-decomposition"),
            DeclarationHandle.Create(Declaration),
            H("Finite residual charge splits around the common blind kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The baseline residual E is the canonical defectRelation. Each "
                        + "single-definition cut U and the blind residual B use the "
                        + "existing conceptKernel and dependent jointKernel; the finite "
                        + "residual E_S uses the canonical finiteSelectionSupplement.")),
                Paragraph(Text(
                    "The theorem first proves that B is exactly E outside the union of "
                        + "all language cuts. Agreement on every language coordinate then "
                        + "shows that B survives every finite selection S.")),
                Paragraph(Text(
                    "An AddContent with NNReal values on an arbitrary IsSetRing supplies "
                        + "finite additivity and monotonicity on the stated algebra. The "
                        + "residual, blind residual, and every single-definition cut are "
                        + "explicitly required to belong to that algebra.")),
                Paragraph(Text(
                    "The countable language, positive candidate costs, nonnegative budget, "
                        + "and positive baseline charge retain the source domain even though "
                        + "the local decomposition does not consume their numerical values. "
                        + "When Gamma is empty, the selected residual is the baseline residual; "
                        + "counting charge on a nonempty Boolean residual compiles all premises."))),
            DescribeRole.Theorem))));

    private static Formula App(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula baseType = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula valueFamily = F.Id("V");
        Formula gamma = Gamma;
        Formula definitions = F.Id("d");
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula candidateCost = F.Id("c");
        Formula budget = F.Id("L");
        Formula selection = F.Id("S");
        Formula setAlgebra = F.Id("A");
        Formula setAlgebraRing = F.Id("hA");
        Formula charge = Nu;
        Formula definition = F.Id("a");
        Formula residual = F.Id("E");
        Formula blind = F.Id("B");
        Formula cut = Seq(F.Id("U"), Underscore, Grp(definition));
        Formula selectedResidual = Seq(F.Id("E"), Underscore, Grp(selection));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nnreal = Seq(Operatorname, Grp(F.Id("NNReal")));
        Formula pairType = Seq(stateType, Sp, Times, Sp, stateType);
        Formula restrictedDefinitions = Seq(
            Open, definitions, Underscore, Grp(F.Id("i")), Close,
            Underscore, Grp(Seq(F.Id("i"), Sp, InMacro, Sp, gamma)));
        Formula residualDefinition = Call("defectRelation", q, target);
        Formula blindDefinition = Call(
            "intersection", residual, Call("jointKernel", restrictedDefinitions));
        Formula cutDefinition = Call(
            "intersection",
            residual,
            Call("complement", Call(
                "conceptKernel", restrictedDefinitions, definition)));
        Formula selectedResidualDefinition = Call(
            "defectRelation",
            Call(
                "conceptJoin",
                q,
                Call(
                    "finiteSelectionSupplement",
                    gamma,
                    definitions,
                    selection)),
            target);
        Formula chargeAt(Formula set) => App(charge, set);
        Formula allCuts = Call(
            "iUnion", Seq(definition, Sp, InMacro, Sp, gamma), cut);
        Formula selectedCuts = Call(
            "iUnion", Seq(definition, Sp, InMacro, Sp, selection), cut);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                baseType, Comma, Sp, targetType, Colon, Sp, type, Comma),
            Seq(
                valueFamily, Colon, Sp, indexType, Sp, To, Sp, type, Comma, Sp,
                gamma, Colon, Sp, Call("Set", indexType), Comma),
            Seq(
                definitions, Colon, Sp, Forall, Sp, F.Id("i"), Colon, Sp,
                indexType, Comma, Sp,
                Call("Concept", stateType, App(valueFamily, F.Id("i"))), Comma),
            Seq(
                q, Colon, Sp, Call("Concept", stateType, baseType), Comma, Sp,
                target, Colon, Sp, Call("Concept", stateType, targetType), Comma),
            Seq(
                candidateCost, Colon, Sp, indexType, Sp, To, Sp, real, Comma, Sp,
                budget, Colon, Sp, nnreal, Comma),
            Seq(
                selection, Colon, Sp, Call("Finset", gamma), Comma, Sp,
                setAlgebra, Colon, Sp, Call("Set", Call("Set", pairType)), Comma),
            Seq(
                setAlgebraRing, Colon, Sp, Call("IsSetRing", setAlgebra), Comma, Sp,
                charge, Colon, Sp, Call("AddContent", nnreal, setAlgebra), Comma),
            Seq(
                Call("Countable", gamma), Sp, Land, Sp,
                Open, Forall, Sp, F.Id("i"), Sp, InMacro, Sp, gamma, Comma, Sp,
                D(0), Sp, Lt, Sp, App(candidateCost, F.Id("i")), Close, Sp, Land),
            Seq(
                D(0), Sp, Leq, Sp, Call("coeReal", budget), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, chargeAt(residualDefinition), Sp, Land),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                residual, Sp, Eq, Sp, residualDefinition, Comma, Sp,
                blind, Sp, Eq, Sp, blindDefinition, Comma),
            Seq(
                cut, Sp, Eq, Sp, cutDefinition, Comma, Sp,
                selectedResidual, Sp, Eq, Sp, selectedResidualDefinition, Comma),
            Seq(
                residual, Sp, InMacro, Sp, setAlgebra, Sp, Land, Sp,
                blind, Sp, InMacro, Sp, setAlgebra, Sp, Land),
            Seq(
                Open, Forall, Sp, definition, Sp, InMacro, Sp, gamma, Comma, Sp,
                cut, Sp, InMacro, Sp, setAlgebra, Close, Sp, Rightarrow),
            Seq(
                blind, Sp, Eq, Sp,
                residual, Sp, Setminus, Sp, allCuts, Sp, Land),
            Seq(
                selectedResidual, Sp, Eq, Sp,
                residual, Sp, Setminus, Sp, selectedCuts, Sp, Land),
            Seq(
                blind, Sp, Subseteq, Sp, selectedResidual, Sp, Land),
            Seq(
                selectedResidual, Sp, InMacro, Sp, setAlgebra, Sp, Land, Sp,
                chargeAt(blind), Sp, Leq, Sp, chargeAt(selectedResidual), Sp, Land),
            Seq(
                chargeAt(selectedResidual), Sp, Eq, Sp,
                chargeAt(blind), Sp, Plus, Sp,
                chargeAt(Seq(selectedResidual, Sp, Setminus, Sp, blind)), Sp, Land),
            Seq(
                Open, gamma, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
                selectedResidual, Sp, Eq, Sp, residual, Close, Dot),
        ]));
    }
}
