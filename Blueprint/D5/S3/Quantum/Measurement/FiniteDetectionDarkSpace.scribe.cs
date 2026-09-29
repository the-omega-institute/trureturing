using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteDetectionDarkSpaceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace."
            + "dark_space_eq_survival_defect_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional repeated-detection dark space is determined after dimension many no-click steps.",
        H("Finite Detection Dark Space"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-detection-dark-space"),
            DeclarationHandle.Create(Declaration),
            H("The dark space is a finite survival-defect kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Q be the no-click operator and let the finite family L_x contain the click operators. "
                        + "Their adjoint products sum with Q^* Q to the identity. The statement also holds in "
                        + "dimension zero, where both sides are trivially true.")),
                Paragraph(Text(
                    "The completeness equation telescopes: the defect of the N-step survival operator is the sum, "
                        + "from n = 0 to N - 1 and over all outcomes x, of the Gram operators of L_x Q^n. "
                        + "Positivity therefore identifies its kernel with the common kernel of those event amplitudes.")),
                Paragraph(Text(
                    "At N equal to the dimension, Cayley-Hamilton expresses every later power of Q through earlier "
                        + "powers. Hence vanishing of the first dimension many event amplitudes propagates to every time."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Multiply(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Adjoint(Formula value) =>
        Seq(value, Caret, Grp(Star));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), x = F.Id("x");
        Formula n = F.Id("n"), q = F.Id("Q"), click = F.Id("L");
        Formula psi = F.Id("psi");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula finD = Call("Fin", d);
        Formula vector = Arrow(finD, complex);
        Formula matrix = Call("Matrix", finD, finD, complex);
        Formula clickAt = Seq(click, Underscore, Grp(x));
        Formula identity = Subscript(F.Id("I"), d);
        Formula completeness = Seq(
            Multiply(Adjoint(q), q), Plus,
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, outcomeType), Sp,
            Multiply(Adjoint(clickAt), clickAt), Sp, Eq, Sp, identity);
        Formula eventOperator = Multiply(clickAt, Power(q, n));
        Formula allEvents = Seq(
            Forall, Sp, Typed(n, nat), Comma, Sp,
            Typed(x, outcomeType), Comma, Sp,
            Call("mulVec", eventOperator, psi), Sp, Eq, Sp, D(0));
        Formula defect = Seq(
            identity, Minus,
            Multiply(Power(Grp(Adjoint(q)), d), Power(q, d)));
        Formula finiteKernel = Seq(
            Call("mulVec", defect, psi), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, Typed(d, nat), Comma, Sp,
            Typed(outcomeType, type), Comma, Sp,
            OpenBracket, Call("Fintype", outcomeType), CloseBracket, Comma,
            RowBreak, Grp(),
            Typed(q, matrix), Comma, Sp,
            Typed(click, Arrow(outcomeType, matrix)), Comma,
            RowBreak, Grp(),
            completeness, Sp, Rightarrow, Sp,
            Forall, Sp, Typed(psi, vector), Comma,
            RowBreak, Grp(),
            Open, allEvents, Close, Sp, Iff, Sp,
            finiteKernel, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
