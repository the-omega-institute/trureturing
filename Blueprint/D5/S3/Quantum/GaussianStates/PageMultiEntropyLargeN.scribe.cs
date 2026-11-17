using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.GaussianStates;

internal sealed class PageMultiEntropyLargeNDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/camargo2026gaussianmultientropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At replica order three, the Page and equal-tripartition configurations have logarithmic large-mode formulas with explicit errors for each fixed squeezing parameter.",
        H("Page and Multi-entropy large-mode formulas"),
        Blocks(
            Describe.Lean(DescribeId.Create("page-me-large-n-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The quantified answer"),
                StatementSource.FromAuthor(Disp(Seq(X("claim"), Eq, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Section 6, printed page 18 (PDF page 19), after equations (63)–(64): “It would be very interesting to obtain similar analytic formulas for the subsystem configurations corresponding to the Page and Multi-entropy times in the large N regime. This would be particularly important to determine the behavior of GM₃³ in other relevant subsystem configurations.” The displayed proposition specifies an answer at replica order three; its coefficients are derived here. The real parameter a is fixed above one. The positive natural k indexes Page sizes (2k,k,k), of total 4k, and equal sizes (k,k,k), of total 3k. The same positive real K bounds both errors for every positive k and may depend on a. GM3 is the normalized Gaussian replica-integral quantity defined in GaussianMultiEntropyAsymptotic; the coercions of k in the logarithms and error denominators are into the reals."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("page-me-large-n-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The two error bounds"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The nine-replica Gram matrix has one constant mode and four paired character classes. Its determinant factors into the corresponding positive scalar factors. The source radical satisfies N²(a²−1)=(N−1)(1−r)²/r, which cancels r from the entropy expression. Substitution at the two tripartitions gives the constants 400/27 and 27/2. The inequalities for log(1+h) and log(1−1/N) give the common choice K=(2+30/(a²−1))/12. This estimate is for each fixed a>1 and does not assert uniformity as a approaches one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("camni2609p"), ResolutionKind.Proved)))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula Fraction(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula RealK => Typed(X("k"), Reals);
    private static Formula DeltaBody => Seq(X("a"), Caret, D(2), Minus, D(1));
    private static Formula Log(Formula value) =>
        new Formula.Apply(Qualified("Real", "log"), [value]);

    private static Formula ErrorBound(bool page)
    {
        Formula total = Product(page ? D(4) : D(3), RealK);
        Formula firstParty = page ? Product(D(2), X("k")) : X("k");
        Formula entropy = new Formula.Apply(Qualified("GaussianMultiEntropyAsymptotic", "GM3"),
            [D(3), firstParty, X("k"), X("k"), X("a")]);
        Formula constant = page ? Fraction(D(4, 0, 0), D(2, 7)) : Fraction(D(2, 7), D(2));
        Formula error = Seq(entropy, Plus,
            Product(Fraction(D(1), D(1, 2)), Log(Product(Parenthesized(total), Parenthesized(DeltaBody)))),
            Minus, Product(Fraction(D(1), D(1, 2)), Log(constant)));
        return Seq(Call("abs", error), Sp, Leq, Sp, Fraction(X("K"), total));
    }

    private static Formula ClaimBody() =>
        All("a", Reals, ImpliesFormula(Seq(D(1), Lt, X("a")),
            Seq(Exists, Sp, Typed(X("K"), Reals), Comma, Sp,
                Parenthesized(And(Seq(D(0), Lt, X("K")),
                    All("k", Naturals, ImpliesFormula(Seq(D(0), Lt, X("k")),
                        And(ErrorBound(true), ErrorBound(false)))))))));
}
