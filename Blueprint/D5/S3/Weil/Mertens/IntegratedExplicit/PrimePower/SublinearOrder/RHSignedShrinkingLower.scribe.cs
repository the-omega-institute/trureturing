using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHSignedShrinkingLowerDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower error scale for shrinking signed prime windows",
        H("The signed discrepancy at arbitrarily late starting points"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-shrinking-lower"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_shrinking_lower"),
            H("Arbitrarily late windows exhibit a logarithmic width error"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The natural cutoff parameters satisfy q=m+1=2r. The original "
                    + "normalized signed residual F(m,u,L) uses endpoints exp(u), exp(u+L) "
                    + "and the power gap with s=1/2−1/q. Set c(m)=μ(q)q/(ms), and use the "
                    + "centered root spectrum S(r,u) with all analytic zero occurrences.")),
                Paragraph(Text("The imaginary parts of the rational root coefficients give "
                    + "a first moment controlled by the reciprocal-square occurrence mass. "
                    + "The odd part of an increment about zero is bounded linearly. The "
                    + "symmetric cusp then gives a positive one-sided logarithmic lower bound.")),
                Paragraph(Text("Integrate the one-sided bound against the original "
                    + "positive exponential weight and normalize by its mass. For each "
                    + "width the normalized primitive increment and the centered series "
                    + "are continuous readouts of the actual phase orbit. Its late returns "
                    + "preserve a fixed fraction of the origin lower bound.")),
                Paragraph(Text("A single width threshold works for every positive lower coefficient below exp(−s)/(8s).")),
                Paragraph(Text("Choose the late threshold so that the decaying arithmetic "
                    + "remainder is smaller than the retained spectral lower bound. "
                    + "The witnessed residual has sign opposite to the nonzero Möbius coefficient. "
                    + "The witness start can depend on the width and the desired threshold."))),
            DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Domain("R"), body);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var h = Id("H");
        var width = Id("L");
        var u = Id("u");
        var tail = Id("U");
        var d = Id("d");
        var zero = Num(0);
        var one = Num(1);

        var residual = Add(Add(Call("F", m, u, width), Call("c", m)),
            Multiply(Call("mu", r), Call("S", r, u)));
        var signedResidual = Multiply(new Formula.Negate(Call("mu", r)), residual);
        var lower = Multiply(Multiply(d, width), Call("log", new Formula.Fraction(one, width)));
        var late = All("U", Domain("R"), Exists("u", And(Le(tail, u), Le(lower, signedResidual))));
        var widths = All("L", Domain("R"), Imp(And(Lt(zero, width), Lt(width, h)), late));
        var s = Subtract(new Formula.Fraction(one, Num(2)),
            new Formula.Fraction(one, Multiply(Num(2), r)));
        var cap = new Formula.Fraction(Call("exp", new Formula.Negate(s)), Multiply(Num(8), s));
        var rates = All("d", Domain("R"), Imp(And(Lt(zero, d), Lt(d, cap)), widths));
        var bounds = Exists("H", And(And(Lt(zero, h), Lt(h, one)), rates));
        var nonzeroM = new Formula.Relation(Call("mu", r), FormulaRelationOperator.NotEqual, zero);
        var cutoffs = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(Num(2), m), And(Equal(Add(m, one), Multiply(Num(2), r)), nonzeroM)), bounds)));
        return F.Disp(Imp(Id("RH"), cutoffs));
    }
}
