using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class MatharA001724Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathar2026a386829");
    private const string Prefix = "D5/S3/Combinatorics/BinomialBases/MatharA001724.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed first-kind Stirling sum defining OEIS A001724 satisfies Mathar's five-lag recurrence for every index at least five. Its ordinary rational formal generating series is annihilated by a nonzero sixth-order differential operator.",
        H("Mathar's recurrence and D-finiteness for A001724"),
        Blocks(
            Node("a", "The full coefficient sum", Sequence(),
                "This is Borislav Crstici's all-index formula in OEIS A001724, revision 43, https://raw.githubusercontent.com/oeis/oeisdata/87b54f574c5f92e16a7c0f5446596eb42715d0ff/seq/A001/A001724.seq. The canonical entry name is Generalized Stirling numbers [n+9,9]_5. The range contains both zero and n; the binomial coefficient is computed in the naturals and cast to the integers. The signed coefficient s is the existing MatharA001722.s: the coefficient of X^K in the integer falling product of length N, including the empty product. No recurrence or initial-value characterization is assumed.", DescribeRole.Definition, true),
            Node("O", "Ordinary formal generating series", Generating(),
                "O is the ordinary formal power series whose nth coefficient is a(n) cast to the rationals. It is not an exponential generating series, and no convergence assertion is involved.", DescribeRole.Definition),
            Node("claim", "Recurrence and the ordinary interpretation", ClaimFormula(),
                "The first assertion is Mathar's recurrence in the formula field of OEIS A001724, revision 43. Every n at least five is included; this onset is an explicit interpretation, not a bound stated in the quoted source. Subtraction in the subscripts is natural subtraction; n is cast to the integers before computing the polynomial coefficients. The second assertion requires a homogeneous polynomial-coefficient differential equation for the same full O, with at least one nonzero coefficient polynomial. The inclusion is the canonical map from rational polynomials to rational formal power series; D is formal differentiation, and its zeroth iterate is the identity.", DescribeRole.Definition, true),
            Node("result", "Recurrence and a homogeneous annihilator", Disp(And(Recurrence(), DFinite())),
                "Let B(n)=(-1)^n times the Taylor translate at -5 of the falling product of length n+4. The Hasse derivative formula identifies its fourth coefficient with the full signed sum. The next falling-product factor gives B(n+1)=B(n)(n+9-X). The five-step linear combination with coefficients -(m+9)^5, 5m^4+190m^3+2710m^2+17195m+40951, -10m^3-300m^2-3005m-10050, 10m^2+210m+1105, -5m-55, 1 equals -X^5 B(m). Taking coefficient four gives the recurrence at n=m+5. For the ordinary series the order-six annihilator has coefficients p(0)=-35+1130X-15480X^2+105124X^3-295245X^4; p(1)=1-45X+1045X^2-13860X^3+99631X^4-304755X^5; p(2)=-5X^2+200X^3-3525X^4+30960X^5-111301X^6; p(3)=10X^4-330X^5+4115X^6-18890X^7; p(4)=-10X^6+240X^7-1600X^8; p(5)=5X^8-65X^9; p(6)=-X^10. Higher coefficient polynomials are zero. Coefficient extraction gives the recurrence multiplied by n+1. Boundary coefficients use a(0)=1, a(1)=35, a(2)=835, a(3)=17360, a(4)=342769. The leading polynomial -X^10 is nonzero. Mathar's wording does not specify ordinary versus exponential series. This canonical statement records the ordinary interpretation; it does not identify that interpretation with a verbatim source specification and does not include the separate exponential-series strengthening. Roberto Blanco Gómez, Proofs and corrections of 306 conjectures in the OEIS, DOI 10.5281/zenodo.23112421, Proposition 7.39 (English PDF p. 33), supplies the exact recurrence and an EGF operator conditional on Jovovic's logarithmic EGF formula. The record publication date is 2026-10-02; the PDF identifies itself as Version 6, dated 2026-10-03. Its assumed equality between that formula's coefficients and the literal signed sum is not authenticated. The present proof instead derives recurrence and ordinary D-finiteness directly from the signed sum; it does not prove that EGF identity. Separate D-finiteness statements, including the transient exponential check, do not imply equality with Jovovic's formula. The shared literature note and problem dossier retain the precise conditional-admission and unread-source limits; no first-solution or worldwide-novelty claim follows.", DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar-a001724-recurrence-dfinite"), ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a001724-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Cast(Formula a, Formula type) => Par(Seq(a, Sp, Colon, Sp, type));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Sum(Formula k, Formula bound, Formula body) =>
        Seq(F.Sum, Underscore, Grp(k, Sp, InMacro, Sp, Call("range", bound)), Sp, Par(body));
    private static Formula Sequence()
    {
        Formula n=F.Id("n"), k=F.Id("k");
        Formula weight=Mul(Mul(Mul(Pow(new Formula.Negate(D(1)),Add(n,k)),
            Cast(Call("choose",Add(k,D(4)),D(4)),Z())),Pow(Cast(D(5),Z()),k)),
            Call("s",Add(n,D(4)),Add(k,D(4))));
        return Disp(All("n",N(),Eq(Call("a",n),Sum(k,Add(n,D(1)),weight))));
    }
    private static Formula Generating()
    {
        Formula n=F.Id("n");
        return Disp(All("n",N(),Eq(Call("coeff",n,F.Id("O")),Cast(Call("a",n),Q()))));
    }
    private static Formula Recurrence()
    {
        Formula n=F.Id("n"), x=Cast(n,Z());
        Formula At(byte lag) => Call("a",Sub(n,D(lag)));
        Formula body=Call("a",n);
        body=Add(body,Mul(Mul(D(5),Sub(new Formula.Negate(x),D(6))),At(1)));
        body=Add(body,Mul(Mul(D(5),Add(Add(Mul(D(2),Pow(x,D(2))),Mul(D(2,2),x)),D(6,1))),At(2)));
        body=Sub(body,Mul(Mul(Mul(D(5),Add(x,D(5))),Add(Add(Mul(D(2),Pow(x,D(2))),Mul(D(2,0),x)),D(5,1))),At(3)));
        Formula quartic=Add(Add(Add(Add(Mul(D(5),Pow(x,D(4))),Mul(D(9,0),Pow(x,D(3)))),Mul(D(6,1,0),Pow(x,D(2)))),Mul(D(1,8,4,5),x)),D(2,1,0,1));
        body=Add(body,Mul(quartic,At(4)));
        body=Sub(body,Mul(Pow(Add(x,D(4)),D(5)),At(5)));
        return All("n",N(),new Formula.Logic(Le(D(5),n),FormulaLogicOperator.Implies,Par(Eq(body,D(0)))));
    }
    private static Formula DFinite()
    {
        Formula r=F.Id("r"), j=F.Id("j");
        Formula nonzero=Ex("j",N(),And(Le(j,r),
            new Formula.Relation(Call("p",j),FormulaRelationOperator.NotEqual,D(0))));
        Formula equation=Eq(Sum(j,Add(r,D(1)),Mul(Call("inclusion",Call("p",j)),
            Call("iterate",F.Id("D"),j,F.Id("O")))),D(0));
        return Ex("r",N(),Ex("p",new Formula.TypeArrow(N(),Call("Polynomial",Q())),And(nonzero,equation)));
    }
    private static Formula ClaimFormula() => Disp(new Formula.Logic(F.Id("claim"),
        FormulaLogicOperator.Iff,Par(And(Recurrence(),DFinite()))));
}
