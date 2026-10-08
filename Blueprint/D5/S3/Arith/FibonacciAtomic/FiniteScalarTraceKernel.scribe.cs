using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FiniteScalarTraceKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(x), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(x), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, F.Iff, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula AddOf(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula SubOf(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula MulOf(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, Par(b));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((term, i) => i == 0 ? new[] { Par(term) }
            : new[] { Sp, Land, Sp, Par(term) })]);
    private static Formula N => V("N");
    private static Formula K => V("K");
    private static Formula P => V("p");
    private static Formula Q => V("s");
    private static Formula M => V("m");
    private static Formula R => V("r");
    private static Formula J => V("j");
    private static Formula Z(Formula modulus, Formula p) => Call("rho", modulus, p);
    private static Formula U(Formula p, Formula j) => Call("U", p, j);
    private static Formula D(Formula j) => SubOf(U(Q, j), U(P, j));
    private static Formula Trace(Formula m, Formula r, Formula p) => Call("T", m, r, p);
    private static Formula TraceEq(Formula m, Formula r) => EqOf(Trace(m, r, P), Trace(m, r, Q));
    private static Formula ZOne(Formula p) => Call("z", Num(2), p, Num(1));
    private static Formula Reading(Formula m, Formula p, Formula j) => Call("c", m, p, j);
    private static Formula Sources(Formula body) => All("p", K, All("s", K, body));
    private static Formula PrefixData(bool shifted) => All("j", N,
        Imp(shifted ? And(Le(Num(1), J), LtOf(J, R)) : LtOf(J, R),
            EqOf(U(P, J), U(Q, J))));

    private static Formula ResultFormula()
    {
        var modulus = AddOf(M, Num(1));
        var kernel = All("m", N, All("r", N, Imp(Le(Num(1), R), Sources(
            IffOf(TraceEq(modulus, R), And(
                EqOf(SubOf(Z(modulus, Q), Z(modulus, P)),
                    Pair(MulOf(new Formula.Negate(Num(3)), D(Num(0))), MulOf(Num(2), D(Num(0))))),
                All("j", N, Imp(Le(AddOf(J, Num(2)), R),
                    EqOf(AddOf(MulOf(Num(2), D(J)), D(AddOf(J, Num(1)))), Num(0))))))))));
        var zero = All("m", N, Sources(IffOf(TraceEq(modulus, Num(0)),
            EqOf(Call("q", Z(modulus, P)), Call("q", Z(modulus, Q))))));
        var one = All("r", N, Sources(TraceEq(Num(1), R)));
        var first = All("m", N, All("p", K, EqOf(Z(modulus, P), Pair(
            SubOf(MulOf(Num(2), Reading(modulus, P, Num(0))),
                MulOf(Num(3), AddOf(Reading(modulus, P, Num(1)), U(P, Num(0))))),
            AddOf(Seq(Minus, Reading(modulus, P, Num(0))),
                MulOf(Num(2), AddOf(Reading(modulus, P, Num(1)), U(P, Num(0)))))))));
        var large = All("m", N, All("r", N,
            Imp(And(Le(Num(3), modulus), Le(Num(2), R)), Sources(
                IffOf(TraceEq(modulus, R), And(PrefixData(false), EqOf(Z(modulus, P), Z(modulus, Q))))))));
        var parity = All("r", N, Imp(Le(Num(1), R), Sources(
            IffOf(TraceEq(Num(2), R), And(PrefixData(true), EqOf(ZOne(P), ZOne(Q)))))));
        var shifted = All("p", K, EqOf(ZOne(P), Pair(
            SubOf(Reading(Num(2), P, Num(0)), Reading(Num(2), P, Num(1))),
            Reading(Num(2), P, Num(1)))));
        var compensation = All("r", N, Imp(Le(Num(1), R), Sources(
            Imp(TraceEq(Num(2), R), EqOf(SubOf(Z(Num(2), Q), Z(Num(2), P)),
                Pair(D(Num(0)), Num(0)))))));
        var fixedCoordinate = All("r", N, Imp(Le(Num(1), R), Sources(
            Imp(And(EqOf(Z(Num(2), P), Z(Num(2), Q)), TraceEq(Num(2), R)),
                EqOf(U(P, Num(0)), U(Q, Num(0)))))));
        var residueDependence = All("m", N, All("r", N, Sources(
            Imp(And(EqOf(Call("omega", P), Call("omega", Q)),
                EqOf(Z(modulus, P), Z(modulus, Q))), TraceEq(modulus, R)))));
        var blindLastDigit = All("m", N, All("r", N, Some("p", K, Some("s", K,
            And(EqOf(Z(modulus, P), Z(modulus, Q)), TraceEq(modulus, R),
                Seq(U(P, R), Sp, Neq, Sp, U(Q, R)))))));
        return And(kernel, zero, one, first, large, parity, shifted, compensation,
            fixedCoordinate, residueDependence, blindLastDigit);
    }

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("finite-scalar-trace-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite scalar deletion histories have an exact congruence kernel and recover different source data at modulus two and at larger moduli.",
        H("Finite Scalar Trace Kernels"), Blocks(
            Paragraph(Text("N denotes the natural numbers. K is the product of LegalDigits with two profinite integers. LegalDigits "
                + "consists of one-sided Boolean streams with no adjacent ones. U(p,j) is the "
                + "natural value zero or one of digit j, and omega(p) is the entire address. "
                + "For each positive modulus h, rho(h,p) projects both initial profinite "
                + "coordinates modulo h. In Lean this existing projection is indexed by m=h-1, "
                + "so every natural m represents exactly the positive modulus m+1. All arithmetic "
                + "in a clause is in ZMod(h), and digit equalities mean actual Boolean equalities.")),
            Definition("trajectory", "Successive deletion vectors",
                "For any commutative ring and input U, z(0)=z and "
                + "z(j+1)=(z(j).second-z(j).first+U(j),z(j).first-U(j)). "
                + "Equivalently z(j)=U(j)*(1,0)+M*z(j+1), with the existing Fibonacci "
                + "map M(x,y)=(y,x+y). This recurrence is applied to each residue projection "
                + "of the initial profinite vector, without imposing a relation between the "
                + "address and that independent vector."),
            Definition("scalarTrace", "Finite scalar history",
                "q(x,y)=2*x+3*y is the existing quantity function. c(h,p,j)=q*z(j) "
                + "modulo h, and T(h,r,p) is the function on Fin(r+1) with values c(h,p,j). "
                + "Thus time zero is included and the horizon r records r+1 readings. "
                + "Only the initial residue and the digits used by the recurrence enter this "
                + "trace. The theorem states this dependence explicitly."),
            Describe.Lean(DescribeId.Create("finite-scalar-trace-kernel-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Exact kernels and short horizons"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first two scalar readings invert the row matrix "
                        + "[[2,3],[1,2]], whose determinant is one. Equal initial readings "
                        + "therefore require the initial-vector difference to equal "
                        + "(-3,2) times the first-digit difference. The scalar recurrence "
                        + "c(j)-c(j+1)-c(j+2)=2*U(j)+U(j+1) gives the residual conditions. "
                        + "Conversely, equal first two readings and equal forcing terms through "
                        + "j+2<=r propagate equality to every time at most r; no forcing equality "
                        + "is required beyond the horizon.")),
                    Paragraph(Text("At horizon zero there is just one scalar comparison; at "
                        + "modulus one every trace is constant. At horizon one the stated "
                        + "inverse reconstructs the initial residue for the actual candidate "
                        + "first digit. For moduli at least three and horizons at least two, "
                        + "the legal adjacent pairs 00,01,10 have distinct codes 0,1,2. "
                        + "The residuals recover precisely the first r digits and the initial "
                        + "residue. Modulo two they recover digits 1 through r-1 and the vector "
                        + "after one deletion. For r=1 that digit interval is empty, and "
                        + "z(1)=(c(0)-c(1),c(1)). Changing the first digit requires the displayed "
                        + "initial-vector compensation; equal fixed initial residues force "
                        + "the first digits to agree. For every modulus and horizon, the "
                        + "all-zero address and the address with a single one at position r, "
                        + "both with zero initial profinite coordinates, give identical traces "
                        + "and different digits at position r. Thus the final observed time "
                        + "does not reveal that digit; at horizon zero this also demonstrates "
                        + "that the scalar reading does not determine the address."))),
                DescribeRole.Theorem))));
}
