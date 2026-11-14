using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannRouterDephasingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One independent router hold in the initialized spatial QRAM has an exact tree kernel and sharp fidelity.",
        H("Single-hold physical router dephasing"),
        Blocks(
            Def("router-geometry", "routerMismatch", "Actual internal router coordinates",
                "addressWord converts the existing recursive Address to its head-first Boolean list. "
                + "routerMismatch compares the router coordinate in each Interior and then both child Trees. "
                + "It excludes all incident and output rails. The loaded trees come from HannSpatialQram.load n n "
                + "on clean inputs. Their comparison is proved by induction on the literal programmed trees: "
                + "equal first bits leave the child comparison; opposite first bits contribute one root "
                + "difference and one occupied path in each distinct subtree. ell below is the length of "
                + "BinaryWordGeometry.lcp of the two addressWords. loadedTree(n,a,b) in the display "
                + "abbreviates the Tree projection of load n n (clean n a b)."),
            Def("router-records", "environmentRecord", "Independent four-dimensional local records",
                "Environment zero is Unit. At a successor it is Option Qutrit times the two child "
                + "environments. none is the common coordinate and some s is the coordinate for label s. "
                + "localRecord has amplitude sqrt(q) at none and sqrt(1-q) at some s. environmentRecord "
                + "multiplies these amplitudes over the actual routers. recordOverlap is the sum of a "
                + "record times the conjugate of the other record over the complete environment basis. "
                + "The local marginal is q X plus (1-q) times the W,zero,one diagonal of X."),
            Def("router-output", "noisyOutput", "Actual continuation and environment marginal",
                "postLoad is exchange, transport, fixed leaf readout, then the inverse of the original "
                + "forward circuit. Its composition with the actual load is the original query. jointOutput "
                + "pulls initialized amplitudes through these permutations and appends the independent "
                + "router records at the hold. noisyOutput is its environment partial trace, as verified "
                + "entry by entry. No gate, bus, address slot or spatial mode receives noise. outputBasis "
                + "at (a,b) is clean n a (b XOR D(a)); idealOutput is the sum of psi(a,b) on this basis."),
            Def("router-fidelity", "minimumFidelity", "Squared fidelity and its minimum",
                "squaredFidelity is the full-State double sum conjugate(idealOutput(s)) times "
                + "noisyOutput(s,t) times idealOutput(t). addressProbability(a) is the sum of normSq "
                + "over both bus amplitudes. addressEnergy is the double address sum p(a)p(a')kernel(a,a'). "
                + "Normalized means the complete address/bus normSq sum is one. kernel is one on the "
                + "diagonal and q to the power 2(n-ell)-1 otherwise. minimumFidelity is "
                + "(1 + sum over j in range n of 2^j q^(2j+1))/2^n. Reindexing j to j+1 gives the "
                + "sum from 1 through n. uniformInput has bus false and amplitude the positive "
                + "inverse square root of 2^n; the theorem also identifies it with 2^(-n/2)."),
            Describe.Lean(DescribeId.Create("physical-router-output-and-exact-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Routing/HannRouterDephasing.result"),
                H("Physical router kernel and least ideal-output fidelity"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All natural depths, every classical D and every normalized complex address/bus "
                    + "amplitude are included. The q interval is closed. At depth zero there are no routers "
                    + "and minimumFidelity is one. Off-span entries vanish. The minimum proof splits address "
                    + "weights by the first bit; the nonnegative remainder is proportional to the squared "
                    + "difference of the two branch masses. Constant kernel row sums give uniform attainment. "
                    + "The router mismatch formula determines the exponent in each clean-output matrix entry. "
                    + "The result assumes this single router hold and ideal remaining gates."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Routing/HannRouterDephasing." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(I(x), InMacro, t), Grp(b));
    private static Formula Conj(Formula a) => C("conj", a);
    private static Formula Both(params Formula[] a) => System.Linq.Enumerable.Aggregate(a, And);
    private static Formula Statement()
    {
        Formula n=I("n"), q=I("q"), d=I("D"), psi=I("psi"), a=I("a"), ap=I("aPrime"),
            b=I("b"), bp=I("bPrime"), s=I("s"), t=I("t"), e=I("e"), x=I("X");
        Formula real=I("Real"), complex=I("Complex"), addr=C("Address",n), state=C("State",n),
            env=C("Environment",n), boolean=I("Bool"), qt=I("Qutrit"),
            amp=Arr(C("Prod",addr,boolean),complex), k=C("kernel",n,q,a,ap),
            f=C("minimumFidelity",n,q), rho=C("noisyOutput",n,q,d,psi),
            joint=C("jointOutput",n,q,d,psi), cleanA=C("clean",n,a,C("xor",b,App(d,a))),
            cleanB=C("clean",n,ap,C("xor",bp,App(d,ap)));
        Formula loadA=C("loadedTree",n,a,b), loadB=C("loadedTree",n,ap,bp);
        Formula local=All("X",C("Matrix",qt,qt,complex),All("s",qt,All("t",qt,
            Eq(Mul(SumOver("e",C("Option",qt),Mul(C("localRecord",q,s,e),Conj(C("localRecord",q,t,e)))),App(x,s,t)),
                Add(Mul(q,App(x,s,t)),Mul(Sub(Num(1),q),C("ite",Eq(s,t),App(x,s,t),Num(0))))))));
        Formula geom=All("a",addr,All("aPrime",addr,All("b",boolean,All("bPrime",boolean,
            And(Eq(C("routerMismatch",n,loadA,loadB),C("ite",Eq(a,ap),Num(0),
                Sub(Mul(Num(2),Sub(n,C("ell",a,ap))),Num(1)))),
                Eq(C("recordOverlap",n,q,loadA,loadB),k))))));
        Formula trace=All("psi",amp,All("s",state,All("t",state,
            Eq(SumOver("e",env,Mul(App(joint,s,e),Conj(App(joint,t,e)))),App(rho,s,t)))));
        Formula entries=All("psi",amp,All("a",addr,All("aPrime",addr,All("b",boolean,All("bPrime",boolean,
            Eq(App(rho,cleanA,cleanB),Mul(Mul(App(psi,C("pair",a,b)),Conj(App(psi,C("pair",ap,bp)))),k)))))));
        Formula outside=All("psi",amp,All("s",state,All("t",state,
            Imp(new Formula.Logic(
                All("a",addr,All("b",boolean,new Formula.Relation(s,FormulaRelationOperator.NotEqual,C("clean",n,a,b)))),
                FormulaLogicOperator.Or,
                All("a",addr,All("b",boolean,new Formula.Relation(t,FormulaRelationOperator.NotEqual,C("clean",n,a,b))))),Eq(App(rho,s,t),Num(0))))));
        Formula fidelity=All("psi",amp,Imp(C("Normalized",n,psi),Both(
            Eq(SumOver("s",state,C("normSq",C("idealOutput",n,d,psi,s))),Num(1)),
            Eq(C("squaredFidelity",n,q,d,psi),C("addressEnergy",n,q,C("addressProbability",n,psi))),
            Le(f,C("re",C("squaredFidelity",n,q,d,psi))))));
        return Disp(All("n",I("Nat"),All("q",real,Imp(Le(Num(0),q),Imp(Le(q,Num(1)),
            All("D",Arr(addr,boolean),Both(local,
                All("t",C("Tree",n),Eq(C("recordOverlap",n,q,t,t),Num(1))),geom,trace,entries,outside,fidelity,
                C("Normalized",n,C("uniformInput",n)),
                Eq(C("squaredFidelity",n,q,d,C("uniformInput",n)),f),
                Eq(C("minimumFidelity",Num(0),q),Num(1)),
                All("ab",C("Prod",addr,boolean),Eq(C("uniformInput",n,I("ab")),
                    C("ite",C("snd",I("ab")),Num(0),C("rpow",Num(2),
                        new Formula.Fraction(C("neg",C("realCast",n)),Num(2)))))))))))));
    }
}
