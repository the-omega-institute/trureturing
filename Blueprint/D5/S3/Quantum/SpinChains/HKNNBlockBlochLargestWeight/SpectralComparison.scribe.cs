using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;
internal sealed class HKNNSpectralComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/liwu2026j1j2rings");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Bloch weights and finite orbit support", H("Normalized Bloch weights and finite orbit support"), Blocks(
            Node("State", "The computational spin basis carries the Hilbert L2 norm; it is not the pointwise supremum norm.", StateFormula(), DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("psiVector", "The integer coefficients of Eq. (6) are embedded in the complex Hilbert state.", psiVectorFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phase", "The phase is exp(2 pi i t j/(2m)). CastComplex embeds every natural or real factor in the complex field; division here is complex division. Momentum t=m is pi, equivalent to -pi.", phaseFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bloch", "Li and Wu, p. 4, Eq. (7): \"|ξ1(k)⟩ = e^{ik/2}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 2⟩, |ξ2(k)⟩ = e^{ik}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 3⟩, |ξ3(k)⟩ = e^{i3k/2}/√3 Σ_{j=0}^{2} e^{ikj} T^j |1, 4⟩, (7)\". The general vector sums all 2m translations before normalization; repeated orbit points add as amplitudes. The full-period and orbit-period sums give the same normalized ray when nonzero. The paper excludes momenta where the Bloch sum vanishes.", blochFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "The squared overlap is divided by the squared Hilbert norms of both vectors. This is the weight in the normalized Bloch basis; the inner product conjugates its first argument.", weightFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spectral_comparison", "The block translations are distinct and its Bloch norm squared is 2m. The translation eigenvalue gives zero overlap at every other momentum. A non-arc Bloch vector is supported on at most 2m configurations with strict coefficient deficits; Cauchy-Schwarz on that support gives the strict normalized weight deficit.", spectralcomparisonFormula(), DescribeRole.Theorem, AssessedProvenance.FromRepo())
        ), []));
    private static DocumentBlock Node(string name, string prose, Formula formula, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hknn-spectralcomparison-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Negate(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Lambda(string v, Formula type, Formula body) => Seq(F.Id(v), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula BigSum(string v, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(F.Id(v), Colon, type)), Sp, body);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Sites(Formula m) => Call("Fin", Mul(D(2), m));
    private static Formula Config(Formula m) => Call("Stationing", Mul(D(2), m));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Iterate(Formula m, Formula j, Formula x) => Call("iterate", Call("shift",m), j, x);
    private static Formula CastC(Formula x) => Call("castComplex",x);
    private static Formula CastR(Formula x) => Call("castReal",x);
    private static Formula BoundWeight(Formula m) => Frac(Mul(CastR(Mul(D(2),m)),Pow(CastR(Call("K",m)),D(2))),Pow(Norm(Call("psiVector",m)),D(2)));
    private static Formula StateFormula()
    {
        Formula m=F.Id("m");
        return All("m",N(),Eq(Call("State",m),Call("EuclideanSpace",C(),Config(m))));
    }
    private static Formula psiVectorFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x");
        return All("m",N(),Eq(Call("psiVector",m),Call("toLp",D(2),Lambda("x",Config(m),CastC(Call("psi",m,x))))));
    }
    private static Formula phaseFormula()
    {
        Formula m=F.Id("m"), t=F.Id("t"), j=F.Id("j");
        return All("m",N(),All("t",Sites(m),All("j",Sites(m),Eq(Call("phase",m,t,j),Call("ComplexExp",Frac(Mul(Mul(Mul(Mul(CastC(D(2)),CastC(Pi)),Named("I")),CastC(Val(t))),CastC(Val(j))),CastC(Mul(D(2),m))))))));
    }
    private static Formula blochFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), t=F.Id("t"), j=F.Id("j");
        return All("m",N(),All("x",Config(m),All("t",Sites(m),Eq(Call("bloch",m,x,t),BigSum("j",Sites(m),Call("smul",Call("phase",m,t,j),Call("single",Iterate(m,Val(j),x),CastC(D(1)))))))));
    }
    private static Formula weightFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), t=F.Id("t");
        return All("m",N(),All("x",Config(m),All("t",Sites(m),Eq(Call("weight",m,x,t),Frac(Pow(Norm(Call("inner",C(),Call("bloch",m,x,t),Call("psiVector",m))),D(2)),Mul(Pow(Norm(Call("bloch",m,x,t)),D(2)),Pow(Norm(Call("psiVector",m)),D(2))))))));
    }
    private static Formula spectralcomparisonFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x"), t=F.Id("t");
        return All("m",N(),Seq(OpenBracket,Call("NeZero",Mul(D(2),m)),CloseBracket,Sp,Imp(Le(D(1),m),And(All("t",Sites(m),Eq(Pow(Norm(Call("bloch",m,Call("block",m),t)),D(2)),CastR(Mul(D(2),m)))),And(All("t",Sites(m),Imp(Eq(Val(t),m),Eq(Call("weight",m,Call("block",m),t),BoundWeight(m)))),And(All("x",Config(m),All("t",Sites(m),Imp(Ne(Call("bloch",m,x,t),D(0)),Imp(Negate(Call("isArc",m,x)),Lt(Call("weight",m,x,t),BoundWeight(m)))))),All("x",Config(m),All("t",Sites(m),Imp(Ne(Val(t),m),Eq(Call("weight",m,x,t),D(0)))))))))));
    }
}
