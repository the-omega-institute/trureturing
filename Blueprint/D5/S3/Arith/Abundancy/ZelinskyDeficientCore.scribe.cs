using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyDeficientCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyDeficientCore.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deficient prime products attain each sufficiently large exponential threshold.",
        H("Quantitative deficient cores with large prime factors"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exponential threshold control at quadratic logarithmic cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Fix any natural cutoff B. There are constants K>0 "
                        + "and T such that for every real t at least T there is a "
                        + "finite set S of primes exceeding B. Put "
                        + "h=product over p in S of (1+1/p) and a=h/(2-h). Then "
                        + "h<2, exp(t)<=a<=3*exp(t), every p in S is less than 2a, "
                        + "and the sum of log(p) over S is at most K*t^2. "
                        + "Distinctness of the prime factors makes their product "
                        + "squarefree, and its abundancy ratio is h.")),
                    Paragraph(Text("Divergence of the reciprocal-prime sum supplies "
                        + "a finite prime product with h at least 2. A minimal "
                        + "crossing set, with its largest prime removed, gives "
                        + "a deficient starting core whose threshold parameter "
                        + "exceeds its prime factors.")),
                    Paragraph(Text("For a large current parameter a, choose a "
                        + "prime p strictly between 2a and 3a. Adjoining p "
                        + "keeps the core deficient and replaces a by "
                        + "a*(p+1)/(p-a), which lies between 3a/2 and 3a. "
                        + "All old and new prime factors remain below twice the "
                        + "new parameter. The first iteration to reach exp(t) "
                        + "therefore has parameter at most 3*exp(t). The number "
                        + "of iterations is linear in t, and each added prime "
                        + "has logarithm bounded linearly in that iteration's "
                        + "index, giving the quadratic total cost.")),
                    Paragraph(Text("The construction supports the primitive "
                        + "non-deficient counting lower bound associated with "
                        + "Zelinsky's Conjectures 11, 13 and 15 in section 3 of "
                        + "arXiv:2005.12115v5 and "
                        + "https://github.com/the-omega-institute/trureturing/issues/31919."))),
                DescribeRole.Theorem))));
}
