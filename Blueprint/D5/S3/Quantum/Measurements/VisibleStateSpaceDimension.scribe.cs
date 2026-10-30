using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class VisibleStateSpaceDimensionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurements/VisibleStateSpaceDimension."
            + "visible_state_space_compact_convex_dimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The visible density-state range is compact and convex, with the expected affine "
            + "dimension bound and complete-observer dimension.",
        H("Visible State-Space Dimension"),
        Blocks(Describe.Lean(
            DescribeId.Create("visible-state-space-compact-convex-dimension"),
            DeclarationHandle.Create(Declaration),
            H("The visible state space has the expected affine dimension"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The visible state is the canonical trace-pairing readout of density "
                        + "matrices, restricted to the supplied Hermitian operator system.")),
                Paragraph(Text(
                    "Density matrices form a compact convex set. A local order-unit "
                        + "perturbation argument identifies the affine directions of their "
                        + "visible image with the readout image of traceless Hermitian "
                        + "directions.")),
                Paragraph(Text(
                    "Evaluation at the identity has codimension one and vanishes on those "
                        + "directions, proving the upper bound. Injectivity of the visible "
                        + "readout makes the centered map injective and preserves all d "
                        + "squared minus one traceless degrees of freedom."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("density-matrix-set-compact-convex"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurements/VisibleStateSpaceDimension."
                    + "density_matrix_set_compact_convex"),
                H("The actual normalized density domain is compact and convex"),
                StatementSource.FromAuthor(DensityDomainFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero dimension this is the set of all complex "
                    + "positive semidefinite matrices of trace one. Singular states are included. "
                    + "The same original supplier is used by the visible-image dimension proof "
                    + "and by the centered physical conjugation-quotient geometry."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula DensityDomainFormula()
    {
        var d = F.Id("d");
        var m = F.Id("M");
        var domain = Call("setOf", Seq(m, InMacro,
            Call("Matrix", Call("Fin", d), Call("Fin", d), Call("Complex")),
            Mapsto, Call("PosSemidef", m), Land, Call("trace", m), Eq, D(1)));
        return Disp(Seq(Forall, Sp, d, InMacro, Call("Nat"), Comma,
            OpenBracket, Call("NeZero", d), CloseBracket, Comma,
            Call("IsCompact", domain), Land, Call("Convex", Call("Real"), domain)));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula system = F.Id("V");
        Formula natural = Call("Nat");
        Formula finD = Call("Fin", d);
        Formula systemType = Call("MatrixOperatorSystem", finD);
        Formula readout = Call("visibleStateReadout", d, system);
        Formula visibleRange = Call("range", readout);
        Formula direction = Call("direction", Call("affineSpanR", visibleRange));
        Formula finrankDirection = Call("finrankR", direction);
        Formula finrankCarrier = Call("finrankR", Call("carrier", system));
        Formula squareMinusOne = Seq(new Formula.Power(d, D(2)), Sp, Minus, Sp, D(1));
        Formula clauses = And(
            Call("IsCompact", visibleRange),
            And(
                Call("ConvexR", visibleRange),
                And(
                    LessEqual(
                        finrankDirection,
                        Seq(finrankCarrier, Sp, Minus, Sp, D(1))),
                    Implies(
                        Call("Injective", readout),
                        Equal(finrankDirection, squareMinusOne)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), natural),
                new Formula.BoundVariable(FormulaIdentifier.Create("V"), systemType),
            ],
            Implies(Call("NeZero", d), clauses)));
    }
}
