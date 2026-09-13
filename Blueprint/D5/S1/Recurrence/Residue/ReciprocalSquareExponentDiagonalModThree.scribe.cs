using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ReciprocalSquareExponentDiagonalModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coefficient of OEIS A397356 is nonzero modulo three exactly when twice its index plus two is a sum of two powers of three.",
        H("OEIS A397356 Modulo Three"),
        Blocks(
            Paragraph(Text("The integer sequence a is the coefficient sequence of generatingSeries "
                + "in ReciprocalSquareExponentDiagonalParity. Its inverse has constant coefficient "
                + "1, linear coefficient -1, and equal coefficients at degree n in its powers "
                + "n^2 and n^2-1 for every n>1. All indices and exponents below are natural numbers.")),
            Paragraph(Text("Over ZMod(3), let S have constant coefficient 1, coefficient -1 at "
                + "each degree (3^j-1)/2 for j>0, and coefficient 0 elsewhere. The index shift "
                + "gives S=1+X+X*S^3. Put Q=S^(-1). The reduction of generatingSeries is S^2.")),
            Node("inverse_cube_diagonal", "The reciprocal square diagonal", DiagonalFormula(),
                "For any S and Q satisfying S=1+X+X*S^3 and S*Q=1, cube extraction gives "
                + "coeff(3m,Q*F^3)=coeff(m,Q*F). Formal differentiation gives "
                + "X*Q'=Q*(Q-1). Together these imply coeff(m,Q^(mt)*(1+Q))=0 for m>0 "
                + "and t congruent to 1 modulo three, by induction stripping factors of three "
                + "from m. Splitting n into its three residue classes proves the diagonal identity."),
            Node("a397356_mod_three", "Hanna's divisibility-by-three conjecture", MainFormula(),
                "Uniqueness of the reciprocal diagonal equations identifies the reduction of "
                + "reciprocalSeries with Q^2, so its inverse reduces to S^2. A sum of two "
                + "powers of three determines the unordered pair of exponents: the sum is "
                + "at least the largest summand and less than three times it. Thus the convolution has "
                + "one nonzero summand for equal indices and two equal nonzero summands for "
                + "distinct indices. Neither multiplicity vanishes modulo three. Exponent "
                + "zero and equal exponents are both allowed.",
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a397356")))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ring() => Call("ZMod", D(3));
    private static Formula Series() => Call("PowerSeries", Ring());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Star, Sp, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula ImpliesF(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);

    private static Formula DiagonalFormula()
    {
        var s = F.Id("S");
        var q = F.Id("Q");
        var n = F.Id("n");
        var x = F.Id("X");
        return Disp(Seq(All("S", Series()), All("Q", Series()),
            ImpliesF(Equal(s, Add(Add(D(1), x), Mul(x, Pow(s, D(3))))),
                ImpliesF(Equal(Mul(s, q), D(1)),
                    Seq(All("n", Nat()), ImpliesF(Seq(D(1), Sp, Lt, Sp, n),
                        Equal(Call("coeff", n, Pow(Pow(q, D(2)), Pow(n, D(2)))),
                            Call("coeff", n, Pow(Pow(q, D(2)), Sub(Pow(n, D(2)), D(1)))))))))));
    }

    private static Formula MainFormula()
    {
        var n = F.Id("n");
        var u = F.Id("u");
        var v = F.Id("v");
        return Disp(Seq(All("n", Nat()), Neg, Sp,
            Par(Seq(D(3), Sp, Mid, Sp, Call("a", n))), Sp, Iff, Sp,
            Par(Seq(Exists, Sp, u, Sp, v, Colon, Sp, Nat(), Comma, Sp,
                Equal(Mul(D(2), Par(Add(n, D(1)))), Add(Pow(D(3), u), Pow(D(3), v)))))));
    }
}
