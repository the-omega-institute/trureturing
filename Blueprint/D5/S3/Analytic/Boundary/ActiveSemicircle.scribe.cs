using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class ActiveSemicircleDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Boundary/ActiveSemicircle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected rational response is negative exactly inside an active "
            + "semicircle and diverges negatively at its right-half-plane pole.",
        H("Active Semicircle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active-semicircle-response-definition"),
                DeclarationHandle.Create(Prefix + "activeSemicircleResponse"),
                H("The reflected rational response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The response adds the two reflected first-order rational terms with "
                        + "centers at horizontal coordinates delta and minus delta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("active-semicircle-criterion"),
                DeclarationHandle.Create(Prefix + "active_semicircle_criterion"),
                H("Negativity is exactly the open semicircle"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source statement is made analytically well-formed by requiring "
                            + "positive delta, positive horizontal coordinate x, and a nonzero "
                            + "pole denominator. The last premise prevents Lean's totalized "
                            + "division by zero from silently assigning a value at the pole.")),
                    Paragraph(Text(
                        "A common denominator is strictly positive on this domain. Its "
                            + "numerator factors as two times x times the signed radial defect, "
                            + "so the response is negative exactly when the point is inside the "
                            + "circle of radius delta centered at the boundary coordinate gamma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-semicircle-boundary-zero"),
                DeclarationHandle.Create(Prefix + "active_semicircle_boundary_zero"),
                H("The non-pole semicircle boundary attains zero"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the bounding circle, away from the rational pole, the radial factor "
                        + "vanishes and the response is exactly zero. This supplies the equality "
                        + "case adjoining the strict negative interior."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-semicircle-axis-endpoints"),
                DeclarationHandle.Create(Prefix + "active_semicircle_axis_endpoints"),
                H("The two axis endpoints lie on the zero boundary"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The circle meets the critical axis at gamma minus delta and gamma plus "
                        + "delta. Both points satisfy the circle equation and attain zero "
                        + "response."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-semicircle-response-unbounded-near-pole"),
                DeclarationHandle.Create(
                    Prefix + "active_semicircle_response_unbounded_near_pole"),
                H("Left approach to the pole is unbounded below"),
                StatementSource.FromAuthor(UnboundedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real bound, an explicit point strictly between the critical "
                        + "axis and the pole has response below that bound. The construction "
                        + "uses x equals delta minus delta divided by n plus two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-semicircle-bounded-background-loses-nonnegativity"),
                DeclarationHandle.Create(
                    Prefix + "active_semicircle_bounded_background_loses_nonnegativity"),
                H("A bounded background cannot preserve nonnegativity"),
                StatementSource.FromAuthor(BoundedBackgroundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any additional contribution bounded above between the axis and the pole "
                        + "is dominated by the negative divergence. Thus the total response is "
                        + "strictly negative at some nearby point."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula Response(
        Formula delta, Formula gamma, Formula x, Formula t) =>
        Apply(F.Id("activeSemicircleResponse"), delta, gamma, x, t);

    private static Formula RadialSquare(
        Formula gamma, Formula x, Formula t) =>
        Seq(
            Square(x), Sp, Plus, Sp,
            Square(Seq(t, Sp, Minus, Sp, gamma)));

    private static Formula PoleDenominator(
        Formula delta, Formula gamma, Formula x, Formula t) =>
        Seq(
            Square(Seq(x, Sp, Minus, Sp, delta)), Sp, Plus, Sp,
            Square(Seq(t, Sp, Minus, Sp, gamma)));

    private static Formula DomainPremises(
        Formula delta, Formula gamma, Formula x, Formula t) =>
        And(
            LessThan(D(0), delta),
            And(
                LessThan(D(0), x),
                NotEqualTo(PoleDenominator(delta, gamma, x, t), D(0))));

    private static Formula CriterionFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula x = F.Id("x");
        Formula t = F.Id("t");
        Formula criterion = IffFormula(
            LessThan(Response(delta, gamma, x, t), D(0)),
            LessThan(RadialSquare(gamma, x, t), Square(delta)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", real), Bound("gamma", real), Bound("x", real), Bound("t", real)],
            Implies(DomainPremises(delta, gamma, x, t), criterion)));
    }

    private static Formula BoundaryFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula x = F.Id("x");
        Formula t = F.Id("t");
        Formula premises = And(
            DomainPremises(delta, gamma, x, t),
            EqualTo(RadialSquare(gamma, x, t), Square(delta)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", real), Bound("gamma", real), Bound("x", real), Bound("t", real)],
            Implies(premises, EqualTo(Response(delta, gamma, x, t), D(0)))));
    }

    private static Formula EndpointClause(
        Formula delta, Formula gamma, Formula endpoint)
    {
        Formula radial = RadialSquare(gamma, D(0), endpoint);
        return And(
            EqualTo(radial, Square(delta)),
            EqualTo(Response(delta, gamma, D(0), endpoint), D(0)));
    }

    private static Formula EndpointFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula left = Seq(gamma, Sp, Minus, Sp, delta);
        Formula right = Seq(gamma, Sp, Plus, Sp, delta);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", real), Bound("gamma", real)],
            Implies(
                LessThan(D(0), delta),
                And(
                    EndpointClause(delta, gamma, left),
                    EndpointClause(delta, gamma, right)))));
    }

    private static Formula UnboundedFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula bound = F.Id("B");
        Formula x = F.Id("x");
        Formula witness = And(
            LessThan(D(0), x),
            And(
                LessThan(x, delta),
                LessThan(Response(delta, gamma, x, gamma), bound)));
        Formula exists = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", real)],
            witness);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", real), Bound("gamma", real), Bound("B", real)],
            Implies(LessThan(D(0), delta), exists)));
    }

    private static Formula BoundedBackgroundFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula background = F.Id("b");
        Formula bound = F.Id("B");
        Formula u = F.Id("u");
        Formula x = F.Id("x");
        Formula boundedAtU = Implies(
            And(LessThan(D(0), u), LessThan(u, delta)),
            LessOrEqual(Apply(background, u), bound));
        Formula bounded = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", real)],
            boundedAtU);
        Formula witness = And(
            LessThan(D(0), x),
            And(
                LessThan(x, delta),
                LessThan(
                    Seq(
                        Response(delta, gamma, x, gamma), Sp, Plus, Sp,
                        Apply(background, x)),
                    D(0))));
        Formula exists = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", real)],
            witness);
        Formula premises = And(LessThan(D(0), delta), bounded);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("delta", real),
                Bound("gamma", real),
                Bound("b", Arrow(real, real)),
                Bound("B", real),
            ],
            Implies(premises, exists)));
    }
}
