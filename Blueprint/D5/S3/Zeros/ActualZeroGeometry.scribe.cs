using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class ActualZeroGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/ActualZeroGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dictionaries for actual xi zeros and standard Mathlib RiemannHypothesis; no assertion of RH.",
        H("Actual zero geometry"), Blocks(
            Describe.Lean(DescribeId.Create("rh-iff-nontrivial-zeros-on-line"),
                DeclarationHandle.Create(Prefix + "rh_iff_nontrivial_zeros_on_line"), H("A001: the nontrivial-zero dictionary"),
                StatementSource.FromAuthor(Iff(RH, OnLine)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("IsNontrivialZero means riemannZeta(rho)=0 and 0<Re(rho)<1. RH is Mathlib's full predicate: for every complex s, riemannZeta(s)=0, exclusion of s=-2(n+1) for every natural n, and s!=1 imply Re(s)=1/2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-xi-central-zeros-real"),
                DeclarationHandle.Create(Prefix + "rh_iff_xi_central_zeros_real"), H("A002: all complex center coordinates"),
                StatementSource.FromAuthor(Iff(RH, CentralReal)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate convention is plus i, with inverse -i(rho-1/2). The frozen inverse laws and actual xi-zero correspondence supply both directions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-xi-right-half-plane"),
                DeclarationHandle.Create(Prefix + "rh_iff_xi_right_half_plane"), H("A003: the entire open right half-plane"),
                StatementSource.FromAuthor(Iff(RH, HalfFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain includes s=1. Growth's bare disk converse consumes this dictionary before its existing summability-to-RH theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nontrivial-zero-cayley-eq"),
                DeclarationHandle.Create(Prefix + "nontrivial_zero_cayley_eq"), H("The guarded Cayley adapter"),
                StatementSource.FromAuthor(All("rho", Complex, Imp(Nontrivial(Id("rho")),
                    Equal(Cayley(Id("rho")), Call("cayleyRatio", Id("rho")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strip positivity proves rho is nonzero before division is simplified. The equality is not asserted at an arbitrary complex zero denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-nontrivial-zero-cayley-norm"),
                DeclarationHandle.Create(Prefix + "rh_iff_nontrivial_zero_cayley_norm"), H("A004: the actual unit-norm condition"),
                StatementSource.FromAuthor(Iff(RH, CayleyUnit)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen Cayley locus theorem supplies both directions. These dictionaries are prerequisites of the source package in DiskEquivalence; that conjunction alone grants no admission."))), DescribeRole.Theorem))));

    internal static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    internal static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    internal static Formula Natural => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    internal static Formula NNReal => F.Seq(Real, F.Underscore, F.Grp(F.Geq, F.D(0)));
    internal static Formula RH => Id("RiemannHypothesis");
    internal static Formula OneHalf => Div(Num(1), Num(2));
    internal static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    internal static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    internal static Formula Norm(Formula a) => new Formula.Norm(a);
    internal static Formula Abs(Formula a) => new Formula.Absolute(a);
    internal static Formula Function(Formula domain, Formula range) => F.Seq(domain, F.To, range);
    internal static Formula Lambda(string variable, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(variable), F.Colon, domain, F.Mapsto, body, F.Close);
    internal static Formula Nontrivial(Formula rho) => Call("IsNontrivialZero", rho);
    internal static Formula Xi(Formula s) => Call("xiReading", s);
    internal static Formula Mobius(Formula z) => Div(Num(1), Subtract(Num(1), z));
    internal static Formula Cayley(Formula rho) => Subtract(Num(1), Div(Num(1), rho));
    internal static Formula Disk(Formula body) => All("z", Complex, Imp(Lt(Norm(Id("z")), Num(1)), body));
    internal static Formula DiskFree => Disk(NotEqual(Call("canonicalXiDisk", Id("z")), Num(0)));
    internal static Formula LiteralDiskFree => Disk(NotEqual(Xi(Mobius(Id("z"))), Num(0)));
    internal static Formula HalfFree => All("s", Complex,
        Imp(Lt(OneHalf, Call("Re", Id("s"))), NotEqual(Xi(Id("s")), Num(0))));
    internal static Formula OnLine => All("rho", Complex,
        Imp(Nontrivial(Id("rho")), Equal(Call("Re", Id("rho")), OneHalf)));
    internal static Formula CentralReal => All("z", Complex,
        Imp(Equal(Xi(Add(OneHalf, Multiply(Id("i"), Id("z")))), Num(0)), Equal(Call("Im", Id("z")), Num(0))));
    internal static Formula CayleyUnit => All("rho", Complex,
        Imp(Nontrivial(Id("rho")), Equal(Norm(Cayley(Id("rho"))), Num(1))));
}
