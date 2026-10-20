using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class MonkmanSirkerConfigurationalEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/monkman2023symmetry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poisson-binomial configurational entropy is nondecreasing under majorization throughout the closed unit cube.",
        H("Monkman–Sirker Configurational Entropy"),
        Blocks(
            Describe.Lean(DescribeId.Create("monkman-sirker-configurational-entropy-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The majorization claim"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Monkman and Sirker, Section 3.3, ‘A conjecture on the concavity of Sc’: " +
                        "\"We note that the configurational entropy Sc = S + (−SN) is a sum of a concave and a convex function. " +
                        "Therefore, one cannot directly apply majorization to Sc based on the already obtained results for S and SN. " +
                        "However, this does not rule our that Sc is also a concave function of the parameters {Ck}. " +
                        "Similar to the original Shepp-Olkin paper [22] we will here just investigate the cases M = 2 and M = 3. " +
                        "Based on these results, we conjecture that Sc({Ck}) is indeed Schur concave and majorization thus applies.\"")),
                    Paragraph(Text(
                    "For every finite dimension M and two vectors c and d in the closed unit cube, " +
                    "moreMixed d c implies F c at most F d. Here F is the sum of binary entropies " +
                    "minus the entropy of the sum of the independent Bernoulli variables; logarithms are natural."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("monkman-sirker-configurational-entropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Majorization increases configurational entropy"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The interior majorization chain reduces the assertion to the pairwise T-transform " +
                        "inequality. For boundary vectors, the same increasing affine map sends both vectors " +
                        "to the open cube and preserves the descending-prefix majorization inequalities. " +
                        "Continuity passes the inequality to the original vectors.")),
                    Paragraph(Text(
                        "This statement includes empty vectors and deterministic Bernoulli parameters. " +
                        "It does not assert joint concavity, strict Schur concavity or classify equality cases. " +
                        "The proof uses general finite-dimensional inequalities rather than bounded enumeration " +
                        "or numerical certification."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("monkman-sirker-2023-configurational-entropy-schur-concavity"),
                    ResolutionKind.Proved)))));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vector() => new Formula.TypeArrow(Call("Fin", F.Id("M")), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Cube(string x) => Seq(Open, All("i", Call("Fin", F.Id("M")),
        Seq(D(0), Le, Call(x, F.Id("i")), Land, Sp, Call(x, F.Id("i")), Le, D(1))), Close);
    private static Formula ClaimFormula() => Disp(All("M", Seq(Mathbb, Grp(F.Id("N"))),
        All("c", Vector(), All("d", Vector(), Seq(
            Cube("c"), Sp, Rightarrow, Sp, Cube("d"), Sp, Rightarrow, Sp,
            Call("moreMixed", F.Id("d"), F.Id("c")), Sp, Rightarrow, Sp,
            Call("F", F.Id("c")), Le, Call("F", F.Id("d")))))));
}
