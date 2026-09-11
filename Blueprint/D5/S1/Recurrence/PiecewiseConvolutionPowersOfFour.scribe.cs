using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PiecewiseConvolutionPowersOfFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a368628");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The piecewise square and fourth-power convolution has odd coefficients exactly at base-four repunits.",
        H("Parity of the Piecewise Convolution Sequence A368628"),
        Blocks(
            Paragraph(Text("All indices and sequence values are natural numbers. Write A for series, "
                + "the ordinary generating series with coefficients seq. The source equation is "
                + "A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2. "
                + "Taking coefficients gives a square convolution at positive even indices and "
                + "a fourth-power convolution at odd indices. The source entry states the parity "
                + "description below as a conjecture; the argument here proves it from that recurrence.")),
            Paragraph(Text("The notation coeff(d,f) extracts degree d, mk forms a power series "
                + "from a coefficient function, and ite selects its second argument when the first "
                + "holds and its third otherwise. Subtraction in indices is natural subtraction. "
                + "The notation cast(v,ZMod(2)) means reduction modulo two.")),
            Node("seq", "The original convolution definition", Definition(),
                "Well-founded recursion defines seq(n) using only values at indices below n. "
                + "The auxiliary coefficient function is zero outside that interval. Since the "
                + "requested coefficient has degree n-1, every factor in its finite convolution "
                + "has index below n; the zero extension cannot change the result. The parity "
                + "pattern is not part of this definition.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("series", "The natural-number generating series",
                Disp(Equal(A(), Call("mk", F.Id("seq")))),
                "A is a power series over the natural numbers, with coefficient n equal to seq(n).",
                DescribeRole.Definition),
            Node("seq_zero", "Initial value", Disp(Equal(S(D(0)), D(1))),
                "The initial clause of the defining recurrence gives the constant coefficient one."),
            Node("seq_recurrence", "The exact coefficient recurrence", Recurrence(),
                "Induction on the exponent of a power shows that equal coefficients through "
                + "degree n-1 give equal coefficients of that power through the same degree. "
                + "Apply this to remove the zero extension in the defining recurrence."),
            Node("seq_even_index_zero", "Positive even indices vanish modulo two",
                Residue(2, 2, D(0)),
                "Apply the existing convolution_pairing theorem to the series g=X A(X squared). "
                + "Its constant coefficient and every even coefficient vanish. The coefficient "
                + "of g squared at degree 4(j+1) is therefore zero, while expansion and the "
                + "factor X squared identify it with degree 2j+1 of A squared. The even-index "
                + "recurrence transfers this cancellation to seq(2j+2)."),
            Node("seq_four_mul_add_three", "Indices congruent to three modulo four vanish",
                Residue(4, 3, D(0)),
                "Frobenius over ZMod(2), applied twice, identifies the fourth power with "
                + "expansion by four. Its coefficients at degrees 4j+2 vanish. The odd-index "
                + "recurrence then gives the displayed sequence value."),
            Node("seq_four_mul_add_one", "Parity descends through indices congruent to one",
                Residue(4, 1, Cast(S(J()))),
                "The same fourth-power identity says its coefficient at degree 4j equals "
                + "the original coefficient at degree j. Reducing the odd-index recurrence "
                + "modulo two yields the equality."),
            Node("a368628_odd_iff", "The parity conjecture for all indices", Characterization(),
                "Strong induction starts at n=0. Positive even indices and indices 4j+3 are "
                + "excluded both by the coefficient reductions and by the residues of 4 to "
                + "a natural power. At n=4j+1, parity descends to j<n, and "
                + "3n+1=4(3j+1) advances the exponent by one. Conversely, a positive exponent "
                + "can be decreased by one, so the same induction proves both directions."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("a368628-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula N() => F.Id("n");
    private static Formula J() => F.Id("j");
    private static Formula A() => F.Id("A");
    private static Formula S(Formula n) => Call("seq", n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Cast(Formula f) => Call("cast", f, Call("ZMod", D(2)));
    private static Formula Exponent() => Call("ite", Call("Even", N()), D(2), D(4));
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);

    private static Formula Definition()
    {
        Formula i = F.Id("i");
        Formula earlier = Call("mk", Par(Seq(i, Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Call("ite", Seq(i, Sp, Lt, Sp, N()), S(i), D(0)))));
        return Disp(Seq(Bound("n"), Equal(S(N()), Call("ite", Equal(N(), D(0)), D(1),
            Coeff(Sub(N(), D(1)), Pow(earlier, Exponent()))))));
    }

    private static Formula Recurrence() => Disp(Seq(Bound("n"), Par(Seq(D(0), Sp, Lt, Sp, N())),
        Sp, Implies, Sp, Equal(S(N()), Coeff(Sub(N(), D(1)), Pow(A(), Exponent())))));

    private static Formula Residue(byte factor, byte offset, Formula value) =>
        Disp(Seq(Bound("j"), Equal(Cast(S(Add(Mul(D(factor), J()), D(offset)))), value)));

    private static Formula Characterization() => Disp(Seq(Bound("n"), Call("Odd", S(N())),
        Sp, Leftrightarrow, Sp, Par(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
            Equal(Add(Mul(D(3), N()), D(1)), Pow(D(4), F.Id("k")))))));
}
