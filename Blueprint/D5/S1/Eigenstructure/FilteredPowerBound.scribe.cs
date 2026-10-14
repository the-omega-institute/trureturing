using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class FilteredPowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite lowering depth gives a truncated binomial bound for powers of noncommuting operators.",
        H("Filtered Operator Power Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("norm-add-pow-le-sum-choose"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/FilteredPowerBound.norm_add_pow_le_sum_choose"),
            H("A contraction and a lowering map"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let K be a nontrivially normed field and E a normed K-vector space. "
                    + "The operators A and B are bounded linear endomorphisms, with the operator norm. "
                    + "Let F be a sequence of submodules with F(0) zero and F(h) equal to E. "
                    + "For every j below h, A preserves F(j+1) and B maps it into F(j). "
                    + "The estimate holds for every natural exponent k if the norm of A is at most one. "
                    + "Neither commutativity, finite dimension nor completeness is needed.")),
                Paragraph(Text("The proof bounds the norm of the kth power applied to a vector in "
                    + "each F(j), simultaneously by induction on k. Splitting the next application "
                    + "into the A and B terms leaves the first vector at the same level and lowers "
                    + "the second by one. The triangle inequality, the operator norm bounds and "
                    + "Pascal's recurrence give the truncated sum. The zero level contains only zero, "
                    + "so the recursion terminates without any assumption that mixed words vanish.")),
                Paragraph(Text("An increasing filtration is a special case; nesting is not needed "
                    + "once the two mapping conditions hold. Height zero is also allowed and forces "
                    + "the space to be trivial. For positive height, binomial coefficients vanish "
                    + "above k, so the displayed sum equals the sum through min(k,h-1). "
                    + "For fixed h it is a polynomial bound in k of degree at most h-1. "
                    + "Application to a physical generation process requires separately identifying "
                    + "its operators, norm and lowering filtration."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Norm(Formula x) => Seq(Lvert, Sp, Lvert, Sp, x, Sp, Rvert, Sp, Rvert);
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);

    private static Formula TheoremFormula()
    {
        Formula K = F.Id("K"), E = F.Id("E"), A = F.Id("A"), B = F.Id("B");
        Formula f = F.Id("F"), h = F.Id("h"), k = F.Id("k"), j = F.Id("j");
        Formula x = F.Id("x"), l = F.Id("l");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula next = App(f, Seq(j, Plus, D(1)));
        Formula mapping = Seq(
            Forall, Sp, j, Sp, InMacro, Sp, nat, Comma, Sp, j, Sp, Lt, Sp, h, Sp, Rightarrow, Sp,
            Forall, Sp, x, Sp, InMacro, Sp, next, Comma, Sp,
            App(A, x), Sp, InMacro, Sp, next, Sp, Land, Sp,
            App(B, x), Sp, InMacro, Sp, App(f, j));
        Formula sum = Seq(Sum, Underscore, Grp(l, Sp, InMacro, Sp, Call("range", h)), Sp,
            Call("choose", k, l), Sp, Cdot, Sp, Norm(B), Caret, Grp(l));
        return Disp(Seq(
            Forall, Sp, K, Sp, Colon, Sp, F.Id("Type"), Comma, Sp, OpenBracket, Call("NontriviallyNormedField", K), CloseBracket, Comma, Esc,
            Forall, Sp, E, Sp, Colon, Sp, F.Id("Type"), Comma, Sp, OpenBracket, Call("NormedAddCommGroup", E), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedSpace", K, E), CloseBracket, Comma, Esc,
            Forall, Sp, A, Comma, Sp, B, Sp, InMacro, Sp, Call("ContinuousLinearEnd", K, E), Comma, Esc,
            Forall, Sp, f, Sp, Colon, Sp, nat, Sp, To, Sp, Call("Submodule", K, E), Comma, Sp,
            Forall, Sp, h, Comma, Sp, k, Sp, InMacro, Sp, nat, Comma, Esc,
            App(f, D(0)), Sp, Eq, Sp, Call("zeroSubmodule", K, E), Sp, Land, Sp,
            App(f, h), Sp, Eq, Sp, Call("wholeSubmodule", K, E), Sp, Land, Esc,
            Open, mapping, Close, Sp, Land, Sp, Norm(A), Sp, Le, Sp, D(1), Sp, Rightarrow, Esc,
            Norm(Seq(Open, A, Plus, B, Close, Caret, Grp(k))), Sp, Le, Sp, sum));
    }
}
