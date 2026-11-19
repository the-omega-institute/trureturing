using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannSignedCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannSignedCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed signed recursion gives unique complex coefficient certificates for actual loaded Hann router records at every height.",
        H("Signed loaded-record coefficients"),
        Blocks(
            Def("signed-local-record", "localRecord", "Specified Fourier coordinates",
                "Set omega=exp(2 pi i/3) and labelIndex(wait)=0, labelIndex(zero)=1, "
                + "labelIndex(one)=2. localRecord(q,s) has coordinates sqrt((1+2q)/3), "
                + "sqrt((1-q)/3) omega^labelIndex(s), sqrt((1-q)/3) omega^(-labelIndex(s)). "
                + "All square roots are the nonnegative real roots. The rate interval is the entire "
                + "closed interval from minus one half to one. The entries need not be real."),
            Def("signed-actual-record", "record", "Literal actual loading and common restrictions",
                "Router n is the existing internal-router index. Environment n is Router n to Fin 3, "
                + "and Address n retains the existing head-first binary order. record n q bus a e is "
                + "the product of localRecord(q(v),loadedLabel n a bus v,e(v)) over all routers. "
                + "loadedLabel is the literal router after the existing actual load. The existing "
                + "loaded_label and vacuum_label supply the programming bridge. Every external qutrit "
                + "bus is allowed. restrict n q b sends v to q(some(b,v)); thus every recursive input "
                + "is a restriction of the same arbitrary heterogeneous assignment. No distinct rates "
                + "are identified. The environment order is root, left child, right child."),
            Def("signed-vacuum-record", "vacuumRecord", "Nonzero vacuum tensor",
                "vacuumRecord n q is the product of the wait local records. It is nonzero throughout "
                + "the rate interval: at a lower-endpoint coordinate use Fourier coordinate one, "
                + "and elsewhere use coordinate zero. This supplies the nonzero factors used in "
                + "the common-scalar tensor argument. At depth zero both record and vacuumRecord are one."),
            Def("signed-synthesis", "synthesis", "Complex coefficient synthesis",
                "Coeff n is Address n to Complex. synthesis n q bus maps x to the environment function "
                + "whose value is the sum of x(a) record(n,q,bus,a,e). embed n b is literal zero "
                + "extension along the first address bit b. The coefficient theorem concerns this map, "
                + "not an operator-space or Schur-superoperator kernel."),
            Def("signed-recursive-output", "outputs", "The prescribed ordered recursion",
                "Output n contains dimension d, an ordered kernel list K, and an optional representative U. "
                + "Its Boolean flag t is U.isSome. At depth zero, d=1, K is empty, and U is the "
                + "constant-one coefficient. At a successor start K with J0(K0) followed by J1(K1), "
                + "preserving both orders. For root rate less than one, d=d0+d1. At rate one, "
                + "subtract one exactly when both child flags are true, and append exactly "
                + "J0(u0)-J1(u1) only in that case. At minus one half, t=t0 and t1 and, when true, "
                + "U=Some(-J0(u0)-J1(u1)). In the open interval t is false and U=None. "
                + "At one, t=t0 or t1 and U prefers Some(J0(u0)) whenever the left flag is true; "
                + "only when it is false and the right flag true use Some(J1(u1)). Otherwise U=None. "
                + "No basis selection, elimination, rescaling, deduplication or optimization changes this list."),
            Def("signed-standard-gram", "standardGram", "The two Gram orientations",
                "recordMatrix has environment rows and address columns and entry record n q bus a e. "
                + "standardGram is its conjugate transpose times itself. densityGram(a,b) instead "
                + "sums record(a,e) conjugate(record(b,e)). Local conjugate-first overlap is one for "
                + "equal labels and q(v) otherwise. The product over actual loaded labels is real, "
                + "so the two Gram orientations coincide. This uses real overlaps, without assuming "
                + "that the Fourier entries themselves are real."),
            Describe.Lean(DescribeId.Create("complete-signed-coefficient-event"),
                DeclarationHandle.Create(Module + "signed_event"),
                H("Complete signed coefficient and Gram certificate"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The statement quantifies over every natural height, every rate assignment in the "
                    + "closed signed interval, every external bus, and every complex coefficient vector. "
                    + "Apply it to restrict at any prefix to obtain all subtree clauses for the original "
                    + "common assignment. The lower endpoint uses the negative sum representative. "
                    + "Below the upper endpoint the local equation forces both child scalars to be "
                    + "the negative vacuum scalar, and in the interior that scalar vanishes. At the "
                    + "upper endpoint the nonzero child vacua force one common scalar. Subtracting "
                    + "the prescribed collision removes it and leaves the two child kernels. Applying "
                    + "child synthesis separates that collision from inherited kernel vectors. This "
                    + "proves completeness and independence of the literal ordered list together with "
                    + "vacuum membership and the prescribed representative equations. Pinned Mathlib "
                    + "finite-dimensional rank-nullity and independent-family span results then give "
                    + "the count and unique coefficients. Its Gram rank and kernel interfaces consume "
                    + "the proved real product bridge. The result is repository-derived; generic tensor "
                    + "intersection or generic basis existence is not claimed as new content. It makes "
                    + "no noisy-continuation, Choi-rank, computability or bit-complexity claim."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Both(params Formula[] a) => System.Linq.Enumerable.Aggregate(a, And);
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(I(x), InMacro, Sp, t), Grp(b));
    private static Formula ProdOver(string x, Formula t, Formula b) =>
        Seq(Prod, Underscore, Grp(I(x), InMacro, Sp, t), Grp(b));

    private static Formula Statement()
    {
        Formula n=I("n"), q=I("q"), bus=I("bus"), v=I("v"), u=I("u"), x=I("x"),
            a=I("a"), b=I("b"), alpha=I("alpha"), beta=I("beta"), i=I("i");
        Formula routers=C("Router",n), addr=C("Address",n), coeff=Arr(addr,I("Complex")),
            output=C("outputs",n,q), dim=C("dimension",output), list=C("kernel",output),
            len=C("length",list), scalars=Arr(C("Fin",len),I("Complex")),
            vacuum=C("vacuumRecord",n,q), synth=C("synthesis",n,q,bus),
            gram=C("standardGram",n,q,bus), density=C("densityGram",n,q,bus);
        Formula Expansion(Formula z) => Eq(x,SumOver("i",C("Fin",len),
            C("smul",App(z,i),C("get",list,i))));
        Formula unique=Ex("alpha",scalars,Both(Expansion(alpha),
            All("beta",scalars,Imp(Expansion(beta),Eq(beta,alpha)))));
        Formula rates=All("v",routers,Both(Le(C("neg",new Formula.Fraction(D(1),D(2))),App(q,v)),
            Le(App(q,v),D(1))));
        Formula overlap=All("a",addr,All("b",addr,Eq(App(gram,a,b),C("ofReal",
            ProdOver("v",routers,C("ite",Eq(C("loadedLabel",n,a,bus,v),
                C("loadedLabel",n,b,bus,v)),D(1),App(q,v)))))));
        Formula conclusions=Both(
            Eq(C("finrank",I("Complex"),C("range",synth)),dim),
            Eq(len,new Formula.Binary(new Formula.Power(D(2),n),FormulaBinaryOperator.Subtract,dim)),
            IffOf(C("mem",vacuum,C("range",synth)),Eq(C("flag",output),I("true"))),
            All("u",coeff,Imp(Eq(C("representative",output),C("some",u)),Eq(App(synth,u),vacuum))),
            All("x",coeff,IffOf(Eq(App(synth,x),D(0)),unique)),overlap,Eq(density,gram),
            Eq(C("ker",C("mulVecLin",density)),C("ker",synth)),Eq(C("rank",density),dim));
        return All("n",I("Nat"),All("q",Arr(routers,I("Real")),
            Imp(rates,All("bus",I("Qutrit"),conclusions))));
    }
}
