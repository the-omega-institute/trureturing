using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class DerivativeHingeMajorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/DerivativeHingeMajorization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ContinuousObservables/deboer2025wignermajorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivative cancellation gives a common convex minimum and two monotone rays.", H("Derivative cancellation and hinge majorization"), Blocks(
            Node("hingeIntegral", All("h", Arrow(Real(), Real()), All("k", Arrow(Real(), Real()), All("T", Real(), All("c", Real(), Eqn(Call("hingeIntegral", Id("h"), Id("k"), Id("T"), Id("c")), Integral("s", Real(), Call("Set.Ioi", D(0)), Call("max", Sub(Call("abs", Add(At(Id("h"), Id("s")), Mul(Id("c"), At(Id("k"), Id("s"))))), Id("T")), D(0)))))))),
                "The integral of the nonnegative part of the thresholded absolute value along the affine family h+c*k. All set integrals use real Lebesgue measure.", false, AssessedProvenance.FromRepo(Source)),
            Node("radial", All("g", Arrow(Real(), Real()), Eqn(Integral("r", Seq(Real(), Times, Real()), null, At(Id("g"), Add(Pow(Call("Prod.fst", Id("r")), D(2)), Pow(Call("Prod.snd", Id("r")), D(2))))), Mul(Qualified("Real.pi"), Integral("s", Real(), Call("Set.Ioi", D(0)), At(Id("g"), Id("s")))))),
                "The squared-radius substitution reduces a planar radial Bochner integral to pi times its integral on the positive half-line. This identity also respects the zero value assigned to nonintegrable Bochner integrals.", true, AssessedProvenance.FromRepo(Source)),
            Node("boundary_cancellation", All("h", Arrow(Real(), Real()), All("k", Arrow(Real(), Real()), Imp(Call("Continuous", Id("h")), Imp(All("x", Real(), Call("HasDerivAt", Id("h"), At(Id("k"), Id("x")), Id("x"))), Imp(Call("MeasureTheory.IntegrableOn", Id("k"), Call("Set.Ioi", D(0))), All("p", Real(), Imp(Leqn(D(0), Id("p")), Imp(All("x", Real(), Imp(Member(Id("x"), Call("Set.Ioo", D(0), Id("p"))), Leqn(D(0), At(Id("k"), Id("x"))))), Imp(All("x", Real(), Imp(Member(Id("x"), Call("Set.Ioi", Id("p"))), Leqn(At(Id("k"), Id("x")), D(0)))), Imp(Eqn(At(Id("h"), D(0)), D(0)), Imp(Call("Filter.Tendsto", Id("h"), Qualified("Filter.atTop"), Call("nhds", D(0))), All("T", Real(), Eqn(Integral("s", Real(), Call("Set.Ioi", D(0)), Mul(At(Id("k"), Id("s")), Call("ite", Ltqn(Id("T"), At(Id("h"), Id("s"))), D(1), D(0)))), D(0)))))))))))))),
                "A differentiable function that starts and ends at zero and has a nonnegative derivative before p and a nonpositive derivative after p has zero derivative integral over every strict superlevel set. Substitution on the two monotone intervals cancels their common endpoint. The remaining endpoint integral tends to zero.", true, AssessedProvenance.FromRepo(Source)),
            Node("hinge_min", All("h", Arrow(Real(), Real()), All("k", Arrow(Real(), Real()), Imp(Call("Continuous", Id("h")), Imp(Call("Continuous", Id("k")), Imp(Call("MeasureTheory.IntegrableOn", Id("h"), Call("Set.Ioi", D(0))), Imp(Call("MeasureTheory.IntegrableOn", Id("k"), Call("Set.Ioi", D(0))), Imp(All("s", Real(), Imp(Member(Id("s"), Call("Set.Ioi", D(0))), Leqn(D(0), At(Id("h"), Id("s"))))), All("T", Real(), All("c", Real(), Imp(Leqn(D(0), Id("T")), Imp(Eqn(Integral("s", Real(), Call("Set.Ioi", D(0)), Mul(At(Id("k"), Id("s")), Call("ite", Ltqn(Id("T"), At(Id("h"), Id("s"))), D(1), D(0)))), D(0)), Leqn(Call("hingeIntegral", Id("h"), Id("k"), Id("T"), D(0)), Call("hingeIntegral", Id("h"), Id("k"), Id("T"), Id("c")))))))))))))),
                "If h is nonnegative on the positive half-line and the derivative-direction superlevel integral vanishes, the thresholded absolute-value integral is minimized at coefficient zero. A pointwise subgradient inequality gives the integral comparison.", true, AssessedProvenance.FromRepo(Source)),
            Node("hinge_convex", All("h", Arrow(Real(), Real()), All("k", Arrow(Real(), Real()), Imp(Call("Continuous", Id("h")), Imp(Call("Continuous", Id("k")), Imp(Call("MeasureTheory.IntegrableOn", Id("h"), Call("Set.Ioi", D(0))), Imp(Call("MeasureTheory.IntegrableOn", Id("k"), Call("Set.Ioi", D(0))), All("T", Real(), Imp(Leqn(D(0), Id("T")), Call("ConvexOn", Real(), Qualified("Set.univ"), Call("hingeIntegral", Id("h"), Id("k"), Id("T"))))))))))),
                "For a nonnegative threshold, the integral is a finite convex function of the affine coefficient. The triangle inequality bounds its values at convex combinations.", true, AssessedProvenance.FromRepo(Source)),
            Node("convex_rays", All("F", Arrow(Real(), Real()), Imp(Call("ConvexOn", Real(), Qualified("Set.univ"), Id("F")), Imp(All("c", Real(), Leqn(At(Id("F"), D(0)), At(Id("F"), Id("c")))), And(Call("MonotoneOn", Id("F"), Call("Set.Ici", D(0))), Call("AntitoneOn", Id("F"), Call("Set.Iic", D(0))))))),
                "A real convex function with a global minimum at zero is monotone on the nonnegative ray and antitone on the nonpositive ray.", true, AssessedProvenance.FromRepo(Source))
        )));

    private static DocumentBlock Node(string name, Formula formula, string prose, bool theorem, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("derivativehingemajorization-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(Id(part))));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Integral(string name, Formula type, Formula? domain, Formula body) =>
        Seq(Int, Underscore, Grp(Seq(Id(name), Colon, type,
            domain is null ? Seq() : Seq(Sp, InMacro, Sp, domain))), Sp, Parenthesized(body));
}
