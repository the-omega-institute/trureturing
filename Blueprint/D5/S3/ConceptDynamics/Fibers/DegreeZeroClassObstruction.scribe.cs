using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class DegreeZeroClassObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Fibers/DegreeZeroClassObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete finite integer family has degree zero but a nontrivial ideal class, "
            + "while zero data is realized by the global element one.",
        H("Degree Zero Does Not Reconstruct Global Data"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-coordinates-are-prime"),
                DeclarationHandle.Create(Prefix + "local_coordinates_are_prime"),
                H("Both local coordinates are genuine prime places"),
                StatementSource.FromAuthor(PrimeCoordinatesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two quotients are identified with ZMod two and ZMod five. "
                        + "Both ideals are prime, and the second is principal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("norm-two-class-is-nontrivial"),
                DeclarationHandle.Create(
                    Prefix + "norm_two_ideal_class_is_nontrivial"),
                H("The norm-two prime has nontrivial ideal class"),
                StatementSource.FromAuthor(NontrivialClassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The square of the norm-two ideal is the principal ideal generated "
                            + "by two, so its fractional ideal is invertible and defines a "
                            + "class-group element.")),
                    Paragraph(Text(
                        "If that class were trivial, the class-group principal criterion "
                            + "would make the norm-two ideal principal, contradicting the "
                            + "existing quadratic norm obstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("obstruction-data-has-explicit-values"),
                DeclarationHandle.Create(Prefix + "obstruction_data_values"),
                H("The local integer family is explicit"),
                StatementSource.FromAuthor(DataValuesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The family has coefficient one at the genuine norm-two prime place "
                        + "and coefficient minus one at a principal prime place. "
                        + "It therefore has finite support with exactly two coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-zero-does-not-give-global-realization"),
                DeclarationHandle.Create(
                    Prefix + "degree_zero_class_data_not_globally_realizable"),
                H("Degree zero is not sufficient for global realization"),
                StatementSource.FromAuthor(NotRealizableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two coefficients sum to zero. Their reconstructed ideal class "
                            + "is nevertheless the nontrivial norm-two class.")),
                    Paragraph(Text(
                        "Every nonzero global element generates a principal fractional "
                            + "ideal and hence the identity class. No such element can match "
                            + "the displayed data even after passing to ideal classes.")),
                    Paragraph(Text(
                        "This is the approved ideal-class downgrade: class compatibility is "
                            + "necessary for exact valuation realization, so failure at this "
                            + "coarser level already prevents reconstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-data-is-realized-by-one"),
                DeclarationHandle.Create(
                    Prefix + "zero_class_data_is_globally_realizable"),
                H("Zero local data is globally realizable"),
                StatementSource.FromAuthor(ZeroRealizableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero family evaluates to the identity class, and the global "
                        + "element one generates a principal fractional ideal with that "
                        + "class. This separates insufficiency from universal failure."))),
                DescribeRole.Theorem))));

    private static Formula LocalData() => F.Id("ell");

    private static Formula PrimeCoordinatesFormula() => Disp(Seq(
        Call("IsPrime", F.Id("P2")), Sp, Land, Sp,
        Call("IsPrime", F.Id("P5")), Sp, Land, Sp,
        Call("IsPrincipal", F.Id("P5")), Dot));

    private static Formula NontrivialClassFormula() => Disp(Seq(
        F.Id("classP2"), Sp, Neq, Sp, D(1), Dot));

    private static Formula DataValuesFormula() => Disp(Seq(
        LocalData(), Open, F.Id("P2"), Close, Sp, Eq, Sp, D(1), Sp, Land, Sp,
        LocalData(), Open, F.Id("P5"), Close, Sp, Eq, Sp, Minus, D(1), Dot));

    private static Formula NotRealizableFormula() => Disp(Seq(
        Call("degree", LocalData()), Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
        Neg, Sp, Call("IdealClassGloballyRealizable", LocalData()), Dot));

    private static Formula ZeroRealizableFormula() => Disp(Seq(
        Call("IdealClassGloballyRealizable", D(0)), Dot));
}
