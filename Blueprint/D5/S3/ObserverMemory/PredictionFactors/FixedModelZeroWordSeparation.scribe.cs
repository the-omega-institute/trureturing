using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class FixedModelZeroWordSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two fixed binary models have separated predictions along all long zero words.",
        H("Fixed-Model Zero-Word Separation"),
        Blocks(
            Paragraph(Text(
                "The hidden bit is initially fair. It emits a report before flipping with "
                    + "probability one quarter. The probability of a zero report is p from "
                    + "hidden bit zero and one minus p from hidden bit one. The emission "
                    + "parameter stays fixed throughout each history.")),
            Node("zeroMass", "Unnormalized zero-word masses", MassFormula(),
                "The two coordinates of v(p,n) are the joint masses of n zero reports and "
                    + "the final hidden bit. Coordinates are numbered zero and one. "
                    + "The recurrence is the column-vector update P diag(p,1-p), with "
                    + "the emission preceding the flip. For the two parameters below both "
                    + "coordinates are positive at every finite length.", DescribeRole.Definition),
            Node("zeroPosterior", "Posterior hidden-bit probability", PosteriorFormula(),
                "Q(p,n) denotes zeroPosterior p n. Dividing the hidden-one mass by "
                    + "the total word mass conditions on the finite zero word.",
                DescribeRole.Definition),
            Node("zeroPrediction", "Current next-zero probability", PredictionFormula(),
                "A(p,n) denotes zeroPrediction p n. The next report is emitted from "
                    + "the current hidden bit; this readout is conditional on the fixed "
                    + "model, without a prior over model indices.", DescribeRole.Definition),
            Node("fixed_model_zero_word_separation", "Uniform rational separation",
                ResultFormula(),
                "For emission parameter one third, the positive mass vector remains in "
                    + "the cone 5 v1 < 9 v0. For emission parameter one quarter, the cross "
                    + "determinant of consecutive mass vectors is positive: its first value "
                    + "is positive and each step multiplies it by 3/32. Normalization "
                    + "therefore gives a strictly increasing posterior. Its value at "
                    + "length three and the other model's invariant bound imply separation "
                    + "at every later length. The theorem concerns the common zero-word "
                    + "family and does not assert statistical indistinguishability of the models.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("fixed-model-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula MassFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula first = Add(Mul(Mul(Rat(D(3), D(4)), p), V(p, n, D(0))),
            Mul(Mul(Rat(D(1), D(4)), Sub(D(1), p)), V(p, n, D(1))));
        Formula second = Add(Mul(Mul(Rat(D(1), D(4)), p), V(p, n, D(0))),
            Mul(Mul(Rat(D(3), D(4)), Sub(D(1), p)), V(p, n, D(1))));
        return Disp(Seq(
            Forall, Sp, p, InMacro, Sp, Reals(), Comma, Sp,
            Call("v", p, D(0)), Eq, Pair(Rat(D(1), D(2)), Rat(D(1), D(2))), Comma, Esc,
            Forall, Sp, n, InMacro, Sp, Naturals(), Comma, Sp,
            Call("v", p, Add(n, D(1))), Eq, Pair(first, second)));
    }

    private static Formula PosteriorFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        return Disp(Seq(Forall, Sp, p, InMacro, Sp, Reals(), Comma, Sp,
            n, InMacro, Sp, Naturals(), Comma, Sp,
            Call("Q", p, n), Eq, Rat(V(p, n, D(1)), Add(V(p, n, D(0)), V(p, n, D(1))))));
    }

    private static Formula PredictionFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        return Disp(Seq(Forall, Sp, p, InMacro, Sp, Reals(), Comma, Sp,
            n, InMacro, Sp, Naturals(), Comma, Sp,
            Call("A", p, n), Eq, Add(p, Mul(Sub(D(1), Mul(D(2), p)), Call("Q", p, n)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula third = Rat(D(1), D(3));
        Formula quarter = Rat(D(1), D(4));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, n, InMacro, Sp, Naturals(), Comma, Sp,
            Call("Q", third, n), Lt, Rat(D(9), D(1, 4)), Sp, Land, Sp,
            Call("A", third, n), Lt, Rat(D(2, 3), D(4, 2)), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, j, InMacro, Sp, Naturals(), Comma, Sp,
            i, Lt, j, Sp, Rightarrow, Sp,
            Call("Q", quarter, i), Lt, Call("Q", quarter, j), Close, Sp, Land, RowBreak,
            Call("Q", quarter, D(3)), Eq, Rat(D(1, 9), D(2, 8)), Sp, Land, Sp,
            Call("A", quarter, D(3)), Eq, Rat(D(3, 3), D(5, 6)), Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, Naturals(), Comma, Sp,
            D(3), Le, Sp, n, Sp, Rightarrow, Sp,
            Rat(Sub(Call("A", quarter, n), Call("A", third, n)), D(2)),
            Gt, Rat(D(1), D(4, 8)), Close,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula V(Formula p, Formula n, Formula index) =>
        new Formula.Subscript(Call("v", p, n), index);
    private static Formula Rat(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
