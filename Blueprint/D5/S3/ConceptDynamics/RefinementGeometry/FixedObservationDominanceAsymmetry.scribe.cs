using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class FixedObservationDominanceAsymmetryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementGeometry/FixedObservationDominanceAsymmetry."
            + "fixed_observation_dominance_asymmetric";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dominance is asymmetric under one fixed indexed observation language.",
        H("Fixed Observation Dominance Asymmetry"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-observation-dominance-asymmetric"),
            DeclarationHandle.Create(Declaration),
            H("Fixed-observation complete dominance is asymmetric"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Diploid genotypes are unordered pairs of alleles. The deterministic "
                        + "realization map sends each genotype and context to an internal state, "
                        + "and the canonical joint readout constructs the fixed observation "
                        + "language's profile.")),
                Paragraph(Text(
                    "Dominance of the left allele means that the left homozygote and shared "
                        + "heterozygote have equal profiles while that heterozygote and the right "
                        + "homozygote have unequal profiles. Reversing dominance would require "
                        + "the latter two profiles to be equal, which is impossible."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula allele = F.Id("A");
        Formula contextType = F.Id("C");
        Formula state = F.Id("X");
        Formula index = F.Id("I");
        Formula coordinate = F.Id("i");
        Formula output = F.Id("O");
        Formula realization = F.Id("realization");
        Formula readout = F.Id("q");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula context = F.Id("c");
        Formula left = F.Id("l");
        Formula right = F.Id("r");
        Formula profile = F.Id("profile");
        Formula dominance = F.Id("dominates");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula unorderedGenotype = Call("Sym2", allele);

        Formula Genotype(Formula first, Formula second) =>
            Call("s", first, second);

        Formula StateAt(Formula first, Formula second) =>
            Call("realization", Genotype(first, second), context);

        Formula ProfileAt(Formula first, Formula second) =>
            Call("profile", StateAt(first, second));

        Formula Dominates(Formula first, Formula second) =>
            Call("dominates", first, second);

        Formula dominanceDefinition = Seq(
            Dominates(
                Seq(left, Colon, Sp, allele),
                Seq(right, Colon, Sp, allele)),
            Colon, Sp, Operatorname, Grp(F.Id("Prop")), Sp, Colon, Sp, Eq, Sp,
            Open,
            ProfileAt(left, left), Sp, Eq, Sp, ProfileAt(left, right), Sp,
            Land, Sp,
            ProfileAt(left, right), Sp, Neq, Sp, ProfileAt(right, right),
            Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, allele, Comma, Sp, contextType, Comma, Sp,
                state, Comma, Sp, index, Colon, Sp, type, Comma),
            Seq(
                output, Colon, Sp, index, Sp, To, Sp, type, Comma),
            Seq(
                realization, Colon, Sp, unorderedGenotype, Sp, To, Sp,
                contextType, Sp, To, Sp, state, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, coordinate, Colon, Sp, index,
                Comma, Sp, state, Sp, To, Sp,
                new Formula.Subscript(output, coordinate), Comma),
            Seq(
                a, Comma, Sp, b, Colon, Sp, allele, Comma, Sp,
                context, Colon, Sp, contextType, Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                profile, Sp, Colon, Sp, Eq, Sp,
                Call("jointReadout", readout), Comma),
            Seq(dominanceDefinition, Sp, Operatorname, Grp(F.Id("in"))),
            Seq(
                Dominates(a, b), Sp, Rightarrow, Sp,
                Neg, Dominates(b, a), Dot),
        ]));
    }
}
