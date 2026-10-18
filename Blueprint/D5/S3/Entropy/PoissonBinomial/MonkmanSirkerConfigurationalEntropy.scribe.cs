using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class MonkmanSirkerConfigurationalEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poisson-binomial configurational entropy is nondecreasing under majorization throughout the closed unit cube.",
        H("Monkman–Sirker Configurational Entropy"),
        Blocks(
            Describe.Lean(DescribeId.Create("monkman-sirker-configurational-entropy-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The majorization claim"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite dimension M and two vectors c and d in the closed unit cube, " +
                    "moreMixed d c implies F c at most F d. Here F is the sum of binary entropies " +
                    "minus the entropy of the sum of the independent Bernoulli variables; logarithms are natural."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("monkman-sirker-configurational-entropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Majorization increases configurational entropy"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The interior majorization chain reduces the assertion to the pairwise T-transform " +
                        "inequality. For boundary vectors, the same increasing affine map sends both vectors " +
                        "to the open cube and preserves the descending-prefix majorization inequalities. " +
                        "Continuity passes the inequality to the original vectors.")),
                    Paragraph(Text(
                        "This statement includes empty vectors and deterministic Bernoulli parameters. " +
                        "It does not assert strict Schur concavity or classify equality cases. " +
                        "The proof uses general finite-dimensional inequalities rather than bounded enumeration " +
                        "or numerical certification."))),
                DescribeRole.Theorem))));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vector() => new Formula.TypeArrow(Call("Fin", F.Id("M")), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Cube(string x) => Seq(Open, All("i", Call("Fin", F.Id("M")),
        Seq(D(0), Le, Call(x, F.Id("i")), Land, Call(x, F.Id("i")), Le, D(1))), Close);
    private static Formula ClaimFormula() => Disp(All("M", Seq(Mathbb, Grp(F.Id("N"))),
        All("c", Vector(), All("d", Vector(), Seq(
            Cube("c"), Sp, Rightarrow, Sp, Cube("d"), Sp, Rightarrow, Sp,
            Call("moreMixed", F.Id("d"), F.Id("c")), Sp, Rightarrow, Sp,
            Call("F", F.Id("c")), Le, Call("F", F.Id("d")))))));
}
