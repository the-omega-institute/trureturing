using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorPolynomialClearanceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact division-free native interior clearance", H("Exact division-free native interior clearance"), Blocks(
            Describe.Lean(DescribeId.Create("interiorpolynomialclearance-numerator-clear"),
                DeclarationHandle.Create(Module + ".numerator_clear"), H("The two full native numerator recurrences"),
                StatementSource.FromAuthor(Disp(Clearance("numerator"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Put J=adj(G), with rows (beta z,-z),(-alpha,1). With A=1+lambda conjugate(lambda), B=1+mu conjugate(mu), e=1+conjugate(lambda)mu and f=conjugate(e), use W=[[Bef,ABe],[ABf,Aef]] and Wstar=transpose(W). The left step is Wstar entrywise times J dagger X J; the right step is J(W entrywise X)J dagger. The right seed is J squared H (J squared) dagger, so neither central inverse-square factor is lost. Universal natural-number induction gives the exact native trialLeft and trialRight scalar identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interiorpolynomialclearance-determinant-clear"),
                DeclarationHandle.Create(Module + ".determinant_clear"), H("Exact real row factors"),
                StatementSource.FromAuthor(Disp(Clearance("determinant"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For d=normSq(delta), a0=1+normSq(lambda), a1=1+normSq(mu), kappa=normSq(1+conjugate(lambda)mu) and Gamma=d a0 a1 kappa, put t=normSq(z). The determinant factors are exactly cL=Gamma^(2p)t^(2p) and cR=Gamma^(2q)d^4 t^(2q+4). At every nonzero trial point in a regular sector, the cleared determinants are cL Re(residual) and cR Im(residual). Targets are arbitrary fixed matrices in this algebraic theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interiorpolynomialclearance-clearance-positive"),
                DeclarationHandle.Create(Module + ".clearance_positive"), H("Strictly positive clearing factors"),
                StatementSource.FromAuthor(Disp(Clearance("positive"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Regularity makes d and kappa strictly positive; a0 and a1 are always strictly positive. Nonzero trial z gives t positive. Every displayed row factor is therefore strictly positive for every natural exterior length. This asserts no positivity preservation by inverse transfer."))), DescribeRole.Theorem),
            Paragraph(Text("These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.")))));

    private static Formula Clearance(string kind)
    {
        var s=Id("s"); var z=Id("z"); var p=Id("p"); var q=Id("q"); var P=Id("P"); var Hh=Id("H");
        var residual=Call("residual",s,p,q,P,Hh,z);
        Formula body = kind == "positive" ? And(Lt(D(0),Call("cL",s,p,z)),Lt(D(0),Call("cR",s,q,z))) :
            kind == "numerator" ? And(
                Eq(Call("leftNumerator",s,z,p,P),Call("smul",Pow(Call("ofReal",Mul(Call("Gamma",s),Call("normSq",z))),p),Call("trialLeft",s,p,P,z))),
                Eq(Call("rightNumerator",s,z,q,Hh),Call("smul",Mul(Pow(Call("ofReal",Mul(Call("Gamma",s),Call("normSq",z))),q),Call("ofReal",Mul(Pow(Call("d",s),D(2)),Pow(Call("normSq",z),D(2))))),Call("trialRight",s,q,Hh,z)))) :
                And(Eq(Call("re",Call("det",Call("leftNumerator",s,z,p,P))),Mul(Call("cL",s,p,z),Call("re",residual))),
                    Eq(Call("re",Call("det",Call("rightNumerator",s,z,q,Hh))),Mul(Call("cR",s,q,z),Call("im",residual))));
        return Bind(kind == "positive" ? [("s",Id("Sector")),("z",Id("Complex")),("p",Id("Nat")),("q",Id("Nat"))] :
            [("s",Id("Sector")),("z",Id("Complex")),("p",Id("Nat")),("q",Id("Nat")),("P",Id("Bond")),("H",Id("Bond"))],
            Imp(And(Call("Regular",s),Ne(z,D(0))),body));
    }

    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b) { for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b); return b; }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
