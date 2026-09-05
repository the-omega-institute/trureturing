using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class FirstOffLineMahlerJumpDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/FirstOffLineMahlerJump.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite off-line root-pair filtration has a positive Mahler jump at its first height.",
        H("First Off-Line Mahler Jump"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mahler-free-energy"),
                DeclarationHandle.Create(Prefix + "mahlerFreeEnergy"),
                H("Mahler free energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each index represents one reflected off-line root pair, using its outer root. "
                        + "The free energy at cutoff T sums multiplicity times log radius over the "
                        + "representatives whose heights are at most T."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-off-line-mahler-jump"),
                DeclarationHandle.Create(Prefix + "first_off_line_mahler_jump"),
                H("The first Mahler jump"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite root-pair carrier makes every cutoff sum finite. A designated "
                            + "root at positive height T0 and the lower-bound hypothesis say that "
                            + "T0 is the first represented off-line height.")),
                    Paragraph(Text(
                        "Every outer radius is strictly greater than one and every multiplicity is "
                            + "positive. Hence each active term is positive by Mathlib's log_pos "
                            + "lemma; these hypotheses explicitly exclude the totalized logarithm's "
                            + "nonpositive branch.")),
                    Paragraph(Text(
                        "No term is active below T0, while the designated pair is active at T0. If "
                            + "it is the unique representative at that height, filtering gives a "
                            + "singleton and the jump is exactly its multiplicity times log radius. "
                            + "Counting one outer representative per reflected pair prevents an "
                            + "unintended factor of two."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula roots = F.Id("R");
        Formula height = F.Id("h");
        Formula radius = F.Id("r");
        Formula multiplicity = F.Id("m");
        Formula firstRoot = F.Id("i0");
        Formula index = F.Id("i");
        Formula cutoff = F.Id("T");
        Formula firstHeight = F.Id("T0");
        Formula energy(Formula t) => Call("FreeEnergy", roots, height, radius, multiplicity, t);

        return Disp(new Formula.Aligned([
            Seq(D(0), Sp, Lt, Sp, firstHeight, Comma, Sp,
                firstRoot, Sp, InMacro, Sp, roots, Comma, Sp,
                Apply(height, firstRoot), Sp, Eq, Sp, firstHeight, Comma),
            Seq(Open, Forall, Sp, index, Sp, InMacro, Sp, roots, Comma, Sp,
                firstHeight, Sp, Leq, Sp, Apply(height, index), Sp, Land, Sp,
                D(1), Sp, Lt, Sp, Apply(radius, index), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, Apply(multiplicity, index), Close, Sp, Rightarrow),
            Seq(Open, Forall, Sp, cutoff, Sp, Lt, Sp, firstHeight, Comma, Sp,
                energy(cutoff), Sp, Eq, Sp, D(0), Close, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, energy(firstHeight), Sp, Land),
            Seq(Open, Open, Forall, Sp, index, Sp, InMacro, Sp, roots, Comma, Sp,
                Apply(height, index), Sp, Eq, Sp, firstHeight, Sp, Rightarrow, Sp,
                index, Sp, Eq, Sp, firstRoot, Close, Sp, Rightarrow),
            Seq(energy(firstHeight), Sp, Eq, Sp,
                new Formula.Binary(
                    Apply(multiplicity, firstRoot),
                    FormulaBinaryOperator.Multiply,
                    Call("log", Apply(radius, firstRoot))),
                Close, Dot),
        ]));
    }
}
