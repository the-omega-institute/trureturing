using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class GammaVerticalReciprocalBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal Gamma function has polynomial-exponential growth on bounded vertical strips.", H("Reciprocal Gamma on vertical strips"), Blocks(
            Describe.Lean(DescribeId.Create("gammaverticalreciprocalbounds-exists-norm-recip-gamma-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le"),
                H("Uniform reciprocal Gamma bound"), StatementSource.FromAuthor(Disp(StripFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every real X there are a real constant C and a natural K such that the bound holds for all real x in [-X,X] and every real y. ComplexGamma denotes complex Gamma, pi the circle constant and i the imaginary unit. The inverse is totalized, so zeros of reciprocal Gamma are included. The proof compares the Gamma modulus product with its half-integer value cosh(pi*y), then uses the entire reciprocal-Gamma recurrence to cover the bounded strip."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gammaverticalreciprocalbounds-integrable-one-add-abs-pow-mul-exp-neg"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.integrable_one_add_abs_pow_mul_exp_neg"),
                H("Integrable polynomial-exponential majorant"), StatementSource.FromAuthor(Disp(All("c", R, Imp(Lt(Num(0), V("c")), All("K", N, Call("Integrable", Map("y", R, Mul(Pow(Add(Num(1), Abs(V("y"))), V("K")), Call("exp", Negate(Mul(V("c"), Abs(V("y"))))))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every positive real c and natural K the displayed real function is Lebesgue integrable. Half of the exponential decay absorbs the polynomial; the remaining half is the two-sided exponential integral."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gammaverticalreciprocalbounds-norm-recip-gamma-sq-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.norm_recip_Gamma_sq_le"),
                H("The retained real Gamma denominator"),StatementSource.FromAuthor(Disp(RetainedFormula())),
                AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text("The existing squared estimate retains Gamma(x)^2 for all real x at least one half. The literal Barnes moving-left estimate consumes it directly, including arbitrarily large x."))),DescribeRole.Theorem))));

    private static Formula RetainedFormula()
    {
        Formula point=Add(V("x"),Mul(Seq(Operatorname,Grp(F.Id("ComplexI"))),V("y")));
        Formula lhs=Pow(Norm(Div(Num(1),Call("ComplexGamma",point))),Num(2));
        Formula rhs=Div(Call("exp",Mul(Seq(Pi,Sp),Abs(V("y")))),Pow(Call("RealGamma",V("x")),Num(2)));
        return All("x",R,Imp(Leq(Div(Num(1),Num(2)),V("x")),All("y",R,Leq(lhs,rhs))));
    }

    private static Formula StripFormula()
    {
        Formula point = Add(V("x"), Mul(Seq(Operatorname, Grp(F.Id("ComplexI"))), V("y")));
        Formula bound = Mul(Mul(V("C"), Pow(Add(Num(1), Abs(V("y"))), V("K"))),
            Call("exp", Div(Mul(Seq(Pi, Sp), Abs(V("y"))), Num(2))));
        Formula line = All("y", R, Leq(Norm(Div(Num(1), Call("ComplexGamma", point))), bound));
        Formula strip = All("x", R, Imp(And(Leq(Negate(V("X")), V("x")),
            Leq(V("x"), V("X"))), line));
        return All("X", R, Some("C", R, Some("K", N, strip)));
    }

    private static Formula R => F.Id("Real");
    private static Formula N => F.Id("Nat");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte digit) => D(digit);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Map(string name, Formula type, Formula value) =>
        Seq(Open, F.Id(name), Colon, type, Sp, Mapsto, Sp, value, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
