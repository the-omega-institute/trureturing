using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class ConfigurationalEntropyStepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/monkman2023symmetry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise smoothing increases the entropy of independent Bernoulli coordinates conditional on their sum.",
        H("Pairwise Configurational Entropy"),
        Blocks(
            Describe.Lean(DescribeId.Create("configurational-entropy-continuous"),
                DeclarationHandle.Create(Prefix + "continuous_F"),
                H("Continuity at the boundary"), StatementSource.FromAuthor(ContinuityFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Each Poisson-binomial mass is a finite sum of products of the Bernoulli parameters " +
                    "and their complements. Continuity of binary entropy and of negative x log x, " +
                    "including zero, therefore gives continuity of F on the whole parameter space."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("configurational-entropy-interior-ttransform"),
                DeclarationHandle.Create(Prefix + "F_le_interiorT"),
                H("An interior T-transform increases F"), StatementSource.FromAuthor(StepFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For two distinct coordinates p at least q, move them to p-s and q+s. " +
                        "The other coordinates give a normalized Poisson-binomial law supported through M-2. " +
                        "Removing the pair expresses the full law as its three-point convolution.")),
                    Paragraph(Text(
                        "At an interior pair p>q, write A=p(1−q) and B=q(1−p), so A−B=p−q. " +
                        "The derivative of F in the smoothing direction factors as " +
                        "(p−q)[(log A−log B)/(A−B)−d], where d is the entropy derivative " +
                        "of the three-point convolution in direction (1,−2,1). The binary part is controlled " +
                        "by the logarithmic bound A1; the convolution part satisfies d≤−log(AB).")),
                    Paragraph(Text(
                        "The entropy-direction bound for the convolution and the logarithmic divided-difference " +
                        "bound show that the derivative of F is nonnegative up to the midpoint. " +
                        "At equal coordinates the derivative is zero. Coordinate permutation invariance " +
                        "handles steps beyond the midpoint. No strictness or equality characterization is asserted."))),
                DescribeRole.Theorem))));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vector() => new Formula.TypeArrow(Call("Fin", F.Id("M")), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula ContinuityFormula() => Disp(All("M", Seq(Mathbb, Grp(F.Id("N"))),
        Call("Continuous", Seq(F.Id("F"), Underscore, Grp(F.Id("M"))))));
    private static Formula StepFormula() => Disp(All("M", Seq(Mathbb, Grp(F.Id("N"))),
        All("x", Vector(), All("y", Vector(), Seq(
            Call("InteriorT", F.Id("x"), F.Id("y")), Sp, Rightarrow, Sp,
            Call("F", F.Id("x")), Le, Call("F", F.Id("y")))))));
}
