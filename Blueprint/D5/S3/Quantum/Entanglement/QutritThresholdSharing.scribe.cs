using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class QutritThresholdSharingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-qutrit threshold encoding hides the input in every single share and "
            + "recovers it from each pair by an explicit permutation unitary.",
        H("Qutrit Threshold Sharing"),
        Blocks(
            Paragraph(Text(
                "All share and input labels lie in ZMod 3, so every label operation is modulo "
                    + "three. Amplitudes are complex numbers. V denotes qutritEncoding, "
                    + "and the coordinate, marginal, and decoder declarations are cyclicShares, "
                    + "singleShareMarginal, and qutritDecoder. Tuples use Lean's right-associated product. "
                    + "The operator Complex.ofReal is the canonical inclusion from real to complex "
                    + "numbers; sqrt is the nonnegative real square root. All displayed "
                    + "fractions are complex-field division.")),
            Describe.Lean(
                DescribeId.Create("qutrit-encoding"),
                Handle("qutritEncoding"),
                H("The common three-share encoding"),
                StatementSource.FromAuthor(EncodingFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/cleve1999share")),
                Blocks(Paragraph(Text(
                    "V is a matrix over the complex numbers with row labels in "
                        + "ZMod 3 x ZMod 3 x ZMod 3 and column labels in ZMod 3. "
                        + "The finite sum is the defining expression, with ite taking its "
                        + "condition, true value, and false value in that order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qutrit-cyclic-shares"),
                Handle("cyclicShares"),
                H("Cyclic coordinate orders"),
                StatementSource.FromAuthor(CyclicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index i has type Fin 3. cyclicShares(i,q) inserts the ordered decoder inputs "
                        + "and spectator into the original coordinates. Indices 0, 1, 2 "
                        + "select ordered pairs (1,2), (2,3), (3,1), respectively; retaining "
                        + "the first argument retains original share 1, 2, 3, respectively. "
                        + "This helper is the coordinate adapter used by both theorems."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qutrit-single-share-marginal"),
                Handle("singleShareMarginal"),
                H("Partial trace retaining the selected share"),
                StatementSource.FromAuthor(MarginalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "singleShareMarginal(i,M) is a matrix over the complex numbers with both "
                        + "row and column labels in ZMod 3. The formula is the defining "
                        + "application of the frozen partialTraceFirst, which sums over equal "
                        + "first-factor indices. In the displayed lambda, p and q have type "
                        + "(ZMod 3 x ZMod 3) x ZMod 3; subscripts denote product projections."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qutrit-decoder"),
                Handle("qutritDecoder"),
                H("The explicit decoder and its inverse"),
                StatementSource.FromAuthor(DecoderFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/cleve1999share")),
                Blocks(Paragraph(Text(
                    "qutritDecoder is an Equiv.Perm (ZMod 3 x ZMod 3). Its toFun and invFun are the "
                        + "two displayed expressions; the left and right inverse laws are "
                        + "proved by ring arithmetic inside this definition. For column amplitudes, "
                        + "Equiv.Perm.permMatrix applied over the complex numbers to the inverse "
                        + "of qutritDecoder has entry one at (x,y) exactly when y = qutritDecoder.symm(x), "
                        + "and zero otherwise. Its action on a basis vector labelled y therefore "
                        + "yields the basis vector labelled qutritDecoder(y). "
                        + "A star superscript denotes conjugate transpose."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qutrit-matrix-unit-marginal"),
                Handle("qutrit_matrix_unit_marginal"),
                H("Partial trace on every matrix unit"),
                StatementSource.FromAuthor(MatrixUnitFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/cleve1999share")),
                Blocks(Paragraph(Text(
                    "single(s,t,1) is the standard Matrix.single s t with complex entry one, and I is the "
                        + "three-dimensional identity matrix. The proof uses the index system "
                        + "j+s=k+t and j+2s=k+2t, which forces s=t and j=k. Cyclic symmetry "
                        + "extends the calculation to all three shares."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-single-share-maximally-mixed"),
                Handle("qutrit_single_share_maximally_mixed"),
                H("Every single share is maximally mixed"),
                StatementSource.FromAuthor(SingleShareFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/cleve1999share")),
                Blocks(Paragraph(Text(
                    "rho ranges over the canonical FiniteStateChannel.DensityState (ZMod 3): "
                        + "positive complex matrices of trace one. val(rho) denotes exactly "
                        + "CStarMatrix.ofMatrix.symm rho.1, the underlying ordinary matrix. "
                        + "Linearity and the frozen trace-one theorem extend the matrix-unit "
                        + "calculation to every input state, including mixed states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-two-share-reconstruction"),
                Handle("qutrit_two_share_reconstruction"),
                H("Every pair reconstructs every input amplitude"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/cleve1999share")),
                Blocks(Paragraph(Text(
                    "mulVec is ordinary matrix action on column amplitudes. Both sides are "
                        + "functions of p in ZMod 3 x ZMod 3. The spectator label r is "
                        + "universally quantified, so this is equality of all three-share "
                        + "amplitudes after decoding. The input psi is arbitrary, hence the "
                        + "identity applies in particular to every normalized pure state. "
                        + "The output is psi tensor the fixed normalized sum of |j,j>. "
                        + "All three choices of i use the same encoding and decoder."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Quantum/Entanglement/QutritThresholdSharing." + name);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Arguments(params Formula[] values)
    {
        var items = new List<Formula>();
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }
        return Parenthesized(Seq([.. items]));
    }

    private static Formula Call(string name, params Formula[] values)
    {
        var parts = name.Split('.');
        var identifier = new List<Formula>();
        for (var index = 0; index < parts.Length; index++)
        {
            if (index > 0) identifier.Add(Dot);
            identifier.Add(F.Id(parts[index]));
        }
        return Seq(Operatorname, Grp([.. identifier]), Arguments(values));
    }

    private static Formula At(Formula function, params Formula[] values) =>
        Seq(function, Arguments(values));

    private static Formula Z() => Call("ZMod", D(3));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Pair() => Seq(Z(), Sp, Times, Sp, Z());
    private static Formula Triple() => Seq(Z(), Sp, Times, Sp, Parenthesized(Pair()));
    private static Formula Matrix(Formula rows, Formula columns) => Call("Matrix", rows, columns, Complex());
    private static Formula Projection(Formula value, byte index) => new Formula.Subscript(value, D(index));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula TimesOf(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Subtract(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);
    private static Formula Inverse(Formula value) => new Formula.Power(value, Seq(Minus, D(1)));
    private static Formula Adjoint(Formula value) => new Formula.Power(value, Star);
    private static Formula DecoderMatrix() => Call("Equiv.Perm.permMatrix", Complex(), Inverse(F.Id("qutritDecoder")));
    private static Formula Normalizer() =>
        new Formula.Fraction(D(1), Call("Complex.ofReal", Seq(Sqrt, Grp(D(3)))));
    private static Formula Third() => new Formula.Fraction(D(1), D(3));
    private static Formula SumOver(Formula variable, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(variable, Colon, Sp, Z())), Sp, Parenthesized(body));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Parenthesized(Seq(variable, Colon, Sp, domain, Sp, Mapsto, Sp, body));
    private static Formula Encoded(Formula matrix) =>
        TimesOf(TimesOf(F.Id("V"), matrix), Adjoint(F.Id("V")));

    private static Formula EncodingFormula()
    {
        var q = F.Id("q"); var s = F.Id("s"); var j = F.Id("j");
        return Disp(All("q", Triple(), All("s", Z(), Equal(At(F.Id("V"), q, s),
            TimesOf(Normalizer(), SumOver(j, Call("ite",
                Equal(q, Arguments(j, Add(j, s), Add(j, TimesOf(D(2), s)))), D(1), D(0))))))));
    }

    private static Formula CyclicFormula()
    {
        var i = F.Id("i"); var q = F.Id("q");
        var a = Projection(q, 1); var b = Projection(Projection(q, 2), 1);
        var c = Projection(Projection(q, 2), 2);
        return Disp(All("i", Call("Fin", D(3)), All("q", Triple(), Equal(
            Call("cyclicShares", i, q), Call("ite", Equal(i, D(0)), q,
                Call("ite", Equal(i, D(1)), Arguments(c, a, b), Arguments(b, c, a)))))));
    }

    private static Formula MarginalFormula()
    {
        var i = F.Id("i"); var m = F.Id("M"); var p = F.Id("p"); var q = F.Id("q");
        Formula Insert(Formula x) => Call("cyclicShares", i, Arguments(Projection(x, 2),
            Projection(Projection(x, 1), 1), Projection(Projection(x, 1), 2)));
        var domain = Seq(Parenthesized(Pair()), Sp, Times, Sp, Z());
        return Disp(All("i", Call("Fin", D(3)), All("M", Matrix(Triple(), Triple()),
            Equal(Call("singleShareMarginal", i, m), Call("partialTraceFirst",
                Lambda(p, domain, Lambda(q, domain, At(m, Insert(p), Insert(q)))))))));
    }

    private static Formula DecoderFormula()
    {
        var p = F.Id("p"); var a = Projection(p, 1); var b = Projection(p, 2);
        return Disp(All("p", Pair(), Seq(
            Parenthesized(Equal(At(F.Id("qutritDecoder"), p), Arguments(Subtract(b, a), Subtract(TimesOf(D(2), b), a)))),
            Sp, Land, Sp,
            Parenthesized(Equal(At(Inverse(F.Id("qutritDecoder")), p), Arguments(Subtract(b, TimesOf(D(2), a)), Subtract(b, a)))))));
    }

    private static Formula MatrixUnitFormula() => Disp(All("i", Call("Fin", D(3)),
        All("s", Z(), All("t", Z(), Equal(
            Call("singleShareMarginal", F.Id("i"), Encoded(Call("single", F.Id("s"), F.Id("t"), D(1)))),
            TimesOf(Call("ite", Equal(F.Id("s"), F.Id("t")), Third(), D(0)), F.Id("I")))))));

    private static Formula SingleShareFormula() => Disp(All("rho", Call("DensityState", Z()),
        All("i", Call("Fin", D(3)), Equal(
            Call("singleShareMarginal", F.Id("i"), Encoded(Call("val", F.Id("rho")))),
            TimesOf(Third(), F.Id("I"))))));

    private static Formula ReconstructionFormula()
    {
        var psi = F.Id("psi"); var i = F.Id("i"); var r = F.Id("r");
        var p = F.Id("p"); var j = F.Id("j");
        var encoded = Call("mulVec", F.Id("V"), psi);
        var input = Lambda(p, Pair(), At(encoded,
            Call("cyclicShares", i, Arguments(Projection(p, 1), Projection(p, 2), r))));
        var output = Lambda(p, Pair(), TimesOf(At(psi, Projection(p, 1)),
            Parenthesized(TimesOf(Normalizer(), SumOver(j, Call("ite",
                Equal(Arguments(Projection(p, 2), r), Arguments(j, j)), D(1), D(0)))))));
        return Disp(All("psi", Parenthesized(new Formula.TypeArrow(Z(), Complex())),
            All("i", Call("Fin", D(3)), All("r", Z(),
                Equal(Call("mulVec", DecoderMatrix(), input), output)))));
    }
}
