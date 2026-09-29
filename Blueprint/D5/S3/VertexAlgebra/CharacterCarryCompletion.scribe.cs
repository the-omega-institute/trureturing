using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class CharacterCarryCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CharacterCarryCompletion.";

    private static Formula Ex(Formula x) => Call("Expand", x);
    private static Formula Co(Formula x, Formula y) => Call("compose", x, y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A section character determines an associative recorded law and the record of every finite fusion tree.",
        H("Character carry and recorded composition"),
        Blocks(
            Paragraph(Text("Let E and C be commutative groups and let ell assign a character "
                + "record to each coarse label, with ell(0)=0. The carry of g and h is "
                + "ell(g)+ell(h)-ell(g+h). A recorded pair (g,c) expands to "
                + "(g,c+ell(g)); its composition has coarse component g+h and record "
                + "c+d+carry(g,h).")),
            Describe.Lean(
                DescribeId.Create("recorded-character-composition"),
                DeclarationHandle.Create(Prefix + "recorded_composition"),
                H("The recorded law is uniquely determined by expansion"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("ell"), Open, D(0), Close, Eq, D(0), Rightarrow, Open, Esc,
                    Open,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Ex(Co(F.Id("x"), F.Id("y"))), Eq,
                    Ex(F.Id("x")), Plus, Ex(F.Id("y")), Close, Sp, Land, Esc,
                    Call("Bijective", F.Id("Expand")), Sp, Land, Esc,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    F.Id("z"), Comma, Sp,
                    Co(Co(F.Id("x"), F.Id("y")), F.Id("z")), Eq,
                    Co(F.Id("x"), Co(F.Id("y"), F.Id("z"))), Close, Sp, Land, Esc,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Co(D(0), F.Id("x")), Eq, F.Id("x"), Eq,
                    Co(F.Id("x"), D(0)), Close, Sp, Land, Esc,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Co(F.Id("x"), F.Id("y")), Eq, Co(F.Id("y"), F.Id("x")),
                    Close, Sp, Land, Esc,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, Exists, Sp, F.Id("y"), Comma, Sp,
                    Co(F.Id("x"), F.Id("y")), Eq, D(0), Sp, Land, Sp,
                    Co(F.Id("y"), F.Id("x")), Eq, D(0), Close, Sp, Land, Esc,
                    Open, Forall, Sp, F.Id("op"), Comma, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Ex(Call("op", F.Id("x"), F.Id("y"))), Eq,
                    Ex(F.Id("x")), Plus, Ex(F.Id("y")), Close, Sp,
                    Rightarrow, Sp, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Call("op", F.Id("x"), F.Id("y")), Eq,
                    Co(F.Id("x"), F.Id("y")), Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Expansion is injective because each character fiber is translated "
                        + "by a fixed value. The carry cancels the section discrepancy, so "
                        + "expanded composition is ordinary addition. The inverse fiber "
                        + "translation makes expansion bijective. It transfers associativity, "
                        + "commutativity, identity, and inverses back to recorded pairs, "
                        + "and forces any other operation with the same expansion law to agree.")),
                    Paragraph(Text("The correction is a coboundary of the chosen section. The "
                        + "result does not assert a nontrivial extension class or construct a "
                        + "fusion category."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-tree-character-record"),
                DeclarationHandle.Create(Prefix + "tree_expansion"),
                H("Every binary tree has the same expanded record formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Comma, Sp,
                    Call("evaluate", F.Id("T")), Eq,
                    Open, Call("total", F.Id("T")), Comma, Sp,
                    Call("characterTotal", F.Id("T")), Minus,
                    F.Id("ell"), Open, Call("total", F.Id("T")), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A leaf carries a coarse label and zero extra record. "
                    + "At each binary node the two recorded values compose. Induction cancels "
                    + "both child section values against the new carry, leaving the sum of "
                    + "all leaf characters minus the character of the total coarse label. "
                    + "The formula holds for every finite branching shape and parenthesization."))),
                DescribeRole.Theorem))));
}
