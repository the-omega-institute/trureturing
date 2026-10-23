using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CentralFactorialTransferExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/CentralFactorialTransferExpansion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central factorial polynomials expand the binary spectral polynomial and its homogenized transfer eigenvalue over a field of characteristic zero.", H("Central factorial transfer coefficients"), Blocks(
        Node("mPoly", "Central factorial polynomials", MPolyBody(), "Page 45, (C.44): \u201cm_j(x) := \u03a0_{k=0}^{j\u22121} [x \u2212 (j \u2212 1 \u2212 2k)], j \u2208 \u2115.\u201d The product is a Polynomial over F; the empty product is one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("dfBinom", "Double factorial binomial coefficients", DfBody(), "Page 47, (C.65): \u201cn_1!!/(n_2!!(n_1 \u2212 n_2)!!).\u201d The integer arguments are sent through Int.toNat before Nat.doubleFactorial, so (\u22121)!! = 0!! = 1. Division is field division.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("scalarEigenvalue", "Transfer eigenvalues", EigenBody(), "Page 45, (C.46): \u201c\u03bb_k(u) = 2(1 + u\u00b2)(1 \u2212 u)^(2k)(1 + u)^(2(n \u2212 1 \u2212 k))\u201d. Here m = n \u2212 1 counts internal edges and l = k counts sign changes. Natural subtraction is truncated.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("scalarExpansion", "Scalar central factorial expansion", ExpansionBody(), "The right side evaluates the central factorial polynomials at m \u2212 2l. Nat.div k 2 is natural-number division; subtraction within natural indices is truncated. Polynomial.eval is written with its evaluation point first.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
        Node("central_spectral_coeff", "The central factorial coefficient identity", CoefficientBody(), "The coefficient of the binary spectral polynomial is the finite double factorial sum. Formal series substitution and a second-order recurrence give the identity; no convergence hypothesis is needed.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
        Node("scalar_settlement", "The scalar transfer identity", ScalarBody(), "The coefficient identity is homogenized at 2u/(1 + u\u00b2); the case 1 + u\u00b2 = 0 is treated directly. The equality holds over every field of characteristic zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
    ), []));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("centralfactorialtransferexpansiondocument-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula MPolyBody() => Field(All("j",N(),Eq(Call("mPoly",X("j")),
        Prod("k",Range(X("j")),Sub(Call("Polynomial.X"),Call("Polynomial.C",
            Sub(Sub(Cast(X("j"),X("F")),D(1)),Mul(D(2),Cast(X("k"),X("F"))))))))));
    private static Formula DfBody() => Field(All("a",Z(),All("b",Z(),Eq(Call("dfBinom",X("a"),X("b")),
        Div(Cast(Call("Nat.doubleFactorial",Call("Int.toNat",X("a"))),X("F")),
            Mul(Cast(Call("Nat.doubleFactorial",Call("Int.toNat",X("b"))),X("F")),
                Cast(Call("Nat.doubleFactorial",Call("Int.toNat",Sub(X("a"),X("b")))),X("F"))))))));
    private static Formula EigenBody() => Field(All("m",N(),All("l",N(),All("u",X("F"),
        Eq(Call("scalarEigenvalue",X("m"),X("l"),X("u")),Mul(Mul(Mul(D(2),Add(D(1),Pow(X("u"),D(2)))),
            Pow(Sub(D(1),X("u")),Mul(D(2),X("l")))),Pow(Add(D(1),X("u")),Mul(D(2),Sub(X("m"),X("l"))))))))));
    private static Formula Expansion(Formula m, Formula l, Formula u) =>
        Mul(D(2),Sum("k",Range(Add(m,D(1))),Mul(
            Mul(Pow(Add(D(1),Pow(u,D(2))),Sub(Add(m,D(1)),X("k"))),Pow(Mul(D(2),u),X("k"))),
            Sum("j",Range(Add(Half(X("k")),D(1))),Mul(CentralCoefficient(Add(m,D(1)),X("k"),X("j")),
                Call("Polynomial.eval",Sub(Cast(m,X("F")),Mul(D(2),Cast(l,X("F")))),
                    Call("mPoly",Sub(X("k"),Mul(D(2),X("j"))))))))));
    private static Formula ExpansionBody() => Field(All("m",N(),All("l",N(),All("u",X("F"),
        Eq(Call("scalarExpansion",X("m"),X("l"),X("u")),Expansion(X("m"),X("l"),X("u")))))));
    private static Formula CoefficientBody() => Field(All("m",N(),All("l",N(),All("k",N(),
        Imp(Le(X("l"),X("m")),Imp(Le(X("k"),X("m")),Eq(
            Call("PowerSeries.coeff",X("k"),Mul(Pow(Add(D(1),Cast(Call("PowerSeries.X"),Call("PowerSeries",X("F")))),Sub(X("m"),X("l"))),
                Pow(Sub(D(1),Call("PowerSeries.X")),X("l")))),
            Sum("j",Range(Add(Half(X("k")),D(1))),Mul(CentralCoefficient(Add(X("m"),D(1)),X("k"),X("j")),
                Call("Polynomial.eval",Sub(Cast(X("m"),X("F")),Mul(D(2),Cast(X("l"),X("F")))),
                    Call("mPoly",Sub(X("k"),Mul(D(2),X("j"))))))))))))),true);
    private static Formula ScalarBody() => Field(All("m",N(),All("l",N(),Imp(Le(X("l"),X("m")),All("u",X("F"),
        Eq(Call("scalarEigenvalue",X("m"),X("l"),X("u")),Call("scalarExpansion",X("m"),X("l"),X("u"))))))),true);

    private static Formula X(string x) => F.Id(x);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return args.Length == 0 ? Seq(Operatorname, Grp([.. parts]))
            : new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, type, Comma, Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula body) =>
        Seq(OpenBracket, Call(name, X("F")), CloseBracket, Sp, body);
    private static Formula Field(Formula body, bool zero = false, bool closed = false) =>
        All("F", Call("Type"), Instance("Field", closed ? Instance("IsAlgClosed",
            Instance("CharZero", body)) : zero ? Instance("CharZero", body) : body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, type));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Sum(string name, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(X(name), InMacro, Sp, domain), Sp, Parenthesized(body));
    private static Formula Prod(string name, Formula domain, Formula body) =>
        Seq(F.Prod, Underscore, Grp(X(name), InMacro, Sp, domain), Sp, Parenthesized(body));
    private static Formula Range(Formula n) => Call("Finset.range",n);
    private static Formula Fact(Formula n) => Call("Nat.factorial",n);
    private static Formula Half(Formula k) => Call("Nat.div",k,D(2));
    private static Formula CentralCoefficient(Formula n, Formula k, Formula j) =>
        Div(Mul(Call("dfBinom", Add(Sub(Sub(Cast(n,Z()),Cast(k,Z())),D(2)),Mul(D(2),Cast(j,Z()))),
            Mul(D(2),Cast(j,Z()))), Pow(Cast(Sub(D(0),D(1)),X("F")),j)),
            Cast(Fact(Sub(k,Mul(D(2),j))),X("F")));
}
