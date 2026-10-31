using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class DiagonalKrausInstrumentFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.";
    private static readonly Formula A = F.Id("A"), B = F.Id("B"), R = F.Id("R");
    private static readonly Formula I = F.Id("I"), O = F.Id("O");
    private static readonly Formula a = F.Id("a"), b = F.Id("b"), r = F.Id("r");
    private static readonly Formula i = F.Id("i"), o = F.Id("o"), q = F.Id("q"), p = F.Id("p");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aggregate Kraus column orthogonality characterizes classical weight evolution of diagonal inputs.",
        H("Diagonal Kraus Instrument Factorization"),
        Blocks(
            Paragraph(Text("Let I and O be finite input and output coordinate types, A a setting type, "
                + "B a finite readable outcome type, and R a finite Kraus type. The complex rectangular "
                + "matrices K(a,b,r) have rows O and columns I. No nonempty-domain assumption is needed. "
                + "The complex vector p is arbitrary; interpreting it as a probability distribution additionally "
                + "requires real nonnegative entries and total mass one. Real weights are embedded in the complex numbers in the matrix formulas.")),
            Paragraph(Text("Write Phi(a,b)(rho) for MatrixMap.of_kraus (K a b) (K a b) rho, the sum of "
                + "K(a,b,r) rho K(a,b,r) adjoint over r. This is an unnormalized branch. The Gram "
                + "condition below concerns distinct output coordinates within each fixed input column "
                + "and is imposed only after summing over r. It permits cancellations between Kraus terms; "
                + "it does not require each Kraus operator to preserve diagonal matrices individually.")),
            Describe.Lean(
                DescribeId.Create("diagonal-instrument-weight"), DeclarationHandle.Create(Prefix + "weight"),
                H("Nonnegative branch weights"), StatementSource.FromAuthor(WeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared complex amplitudes are summed over the discarded Kraus "
                    + "index. The outcome b is retained, so these weights need not sum to one within a branch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("diagonal-instrument-entry-expansion"),
                DeclarationHandle.Create(Prefix + "diagonal_entry_expansion"),
                H("Entries of a Kraus map on a diagonal input"),
                StatementSource.FromAuthor(EntryExpansionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each output entry is the input-weighted sum of the corresponding Kraus column Gram coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-instrument-factorization"),
                DeclarationHandle.Create(Prefix + "diagonal_instrument_factorization"),
                H("Orthogonality, factorization, and stochastic normalization"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Global completeness normalizes the sum over outcomes b and output "
                        + "coordinates o for every setting a and input i. Matrix multiplication against a "
                        + "diagonal input expands each entry into a weighted sum of column Gram coefficients. "
                        + "Vanishing off-diagonal Gram sums remove every off-diagonal output entry. On the "
                        + "diagonal, the same coefficients are squared amplitudes and hence give W. Conversely, "
                        + "testing p equal to each coordinate basis distribution isolates every Gram coefficient.")),
                    Paragraph(Text("The total map is the sum of all outcome branches. Its canonical quantum "
                        + "channel is supplied by finite_kraus_quantum_channel applied to the product Kraus "
                        + "index B times R. Complete positivity and trace preservation use that existing theorem.")),
                    Paragraph(Text("For a nonnegative probability input, the branch mass is the trace of "
                        + "its output, equal to the sum of its output diagonal coefficients. A conditional "
                        + "trace-one state is obtained by dividing by this real mass only when it is strictly "
                        + "positive. Zero-mass branches carry no conditional-state assignment. The equivalence "
                        + "and normalization are the formal claims here; conditioning is their probability "
                        + "interpretation under the stated positivity assumptions.")),
                    Paragraph(Text("This finite-dimensional result supplies a mathematical criterion for a "
                        + "quantum bridge. Applying it to AURIC FIB requires an independently specified Kraus "
                        + "family and proofs of completeness and the Gram condition. FIB coordinates, source "
                        + "ancestry, physical implementation, observable precision, and resource costs are "
                        + "additional data; none is inferred from this factorization."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula SumOver(Formula index, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, type), Sp, Grp(body));

    private static Formula Adj(Formula body) => Seq(Grp(body), Caret, Grp(Star));
    private static Formula Entry(Formula row) => Call("K", a, b, r, row, i);
    private static Formula W => Call("W", a, b, o, i);

    private static Formula Context(Formula body, bool completeTypes)
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula types = Seq(Forall, Sp, I, Comma, O, Comma, A, Comma, B, Comma, R,
            Colon, Sp, F.Id("Type"), Comma, Sp);
        Formula finite = completeTypes
            ? Seq(OpenBracket, Call("Fintype", I), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", I), CloseBracket, Sp,
                OpenBracket, Call("Fintype", O), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", O), CloseBracket, Sp,
                OpenBracket, Call("Fintype", B), CloseBracket, Sp,
                OpenBracket, Call("Fintype", R), CloseBracket, Comma, Sp)
            : Seq(OpenBracket, Call("Fintype", R), CloseBracket, Comma, Sp);
        return Seq(types, finite, Forall, Sp, F.Id("K"), Colon, Sp,
            A, Sp, To, Sp, B, Sp, To, Sp, R, Sp, To, Sp, Call("Matrix", O, I, complex),
            Comma, RowBreak, Grp(), body);
    }

    private static Formula WeightFormula() => Disp(Context(Seq(
        Forall, Sp, a, Colon, Sp, A, Comma, Sp, b, Colon, Sp, B, Comma, Sp,
        o, Colon, Sp, O, Comma, Sp, i, Colon, Sp, I, Comma, Sp,
        W, Sp, Eq, Sp, SumOver(r, R, Call("normSq", Entry(o)))), false));

    private static Formula EntryExpansionFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula k = F.Id("K");
        Formula gram = Multiply(Call("K", r, o, i),
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("starRingEnd"))),
                [complex, Call("K", r, q, i)]));
        Formula channel = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("MatrixMap"), Dot, F.Id("of"), Underscore, Grp(F.Id("kraus")))),
            [k, k, new Formula.Apply(Seq(Operatorname,
                Grp(F.Id("Matrix"), Dot, F.Id("diagonal"))), [p]), o, q]);
        return Disp(Seq(Forall, Sp, I, Comma, O, Comma, R, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", I), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", I), CloseBracket, Sp,
            OpenBracket, Call("Fintype", R), CloseBracket, Comma, Sp,
            Forall, Sp, k, Colon, Sp, R, Sp, To, Sp, Call("Matrix", O, I, complex), Comma, Sp,
            Forall, Sp, p, Colon, Sp, I, Sp, To, Sp, complex, Comma, Sp,
            Forall, Sp, o, Comma, q, Colon, Sp, O, Comma, Sp,
            Equal(channel, SumOver(i, I, Multiply(Parenthesized(SumOver(r, R, gram)), Call("p", i))))));
    }

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("K", a, b, r);
        Formula complete = Seq(Forall, Sp, a, Sp, InMacro, Sp, A, Comma, Sp,
            SumOver(b, B, SumOver(r, R, Seq(Adj(matrix), Sp, matrix))), Sp, Eq, Sp,
            Call("identity", I));
        Formula positive = Seq(Forall, Sp, a, Comma, b, Comma, o, Comma, i, Comma, Sp,
            D(0), Sp, Leq, Sp, W);
        Formula normalized = Seq(Forall, Sp, a, Comma, i, Comma, Sp,
            SumOver(b, B, SumOver(o, O, W)), Sp, Eq, Sp, D(1));
        Formula gram = Seq(Forall, Sp, a, Comma, b, Comma, i, Comma, o, Comma, q, Comma, Sp,
            o, Sp, Neq, Sp, q, Sp, Rightarrow, Sp,
            SumOver(r, R, Seq(Entry(o), Sp, Call("conj", Entry(q)))), Sp, Eq, Sp, D(0));
        Formula factor = Seq(Forall, Sp, p, Colon, Sp, I, Sp, To, Sp, complex, Comma, Sp,
            Forall, Sp, a, Comma, b, Comma, Sp,
            Call("Phi", a, b, Call("diag", p)), Sp, Eq, Sp,
            Call("diag", Seq(o, Sp, Mapsto, Sp, SumOver(i, I, Seq(W, Sp, Call("p", i))))));
        Formula channel = Seq(Forall, Sp, a, Comma, Sp, Exists, Sp, F.Id("C"), Colon, Sp,
            Call("QuantumChannel", I, O), Comma, Sp, Forall, Sp, Rho, Colon, Sp,
            Call("Matrix", I, I, Seq(Mathbb, Grp(F.Id("C")))), Comma, Sp,
            Call("matrixAction", F.Id("C"), Rho), Sp, Eq, Sp,
            SumOver(b, B, Call("Phi", a, b, Rho)));
        return Disp(Context(Seq(Parenthesized(complete), Sp, Rightarrow, RowBreak, Grp(),
            Parenthesized(positive), Sp, Land, Sp, Parenthesized(normalized), Sp, Land, RowBreak, Grp(),
            Parenthesized(Seq(Parenthesized(gram), Sp, Iff, Sp, Parenthesized(factor))),
            Sp, Land, RowBreak, Grp(), Parenthesized(channel)), true));
    }
}
