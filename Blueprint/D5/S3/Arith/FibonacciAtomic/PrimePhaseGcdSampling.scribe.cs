using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimePhaseGcdSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling.";
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int => Seq(Mathbb, Grp(F.Id("Z")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp prime Fibonacci phase identification and simultaneous bounded natural counterexamples.",
        H("Prime Phase Gcd Sampling"),
        Blocks(
            Paragraph(Text("F(0)=0 and F(1)=1. All queried times are positive natural numbers. "
                + "The signed reading takes the absolute value of the entire linear combination. "
                + "The source reading uses actual nonnegative coordinates, not merely residue labels.")),
            Node("localGcd", "Signed local reading", Disp(All(F.Id("p"), Nat,
                All(Vars("n", "z"), Int, All(F.Id("k"), Nat, Equal(Call("G", Ids("p", "n", "z", "k")),
                Call("gcd", Call("abs", Seq(Call("F", Seq(F.Id("k"), Minus, D(1))), Cdot, Sp, F.Id("n"),
                    Plus, Call("F", F.Id("k")), Cdot, Sp, F.Id("z"))), F.Id("p"))))))),
                "The state coordinates n,z are integers and the modulus p is natural.",
                DescribeRole.Definition),
            Node("sourceGcd", "Natural source reading", Disp(All(Vars("H", "a", "b", "k"), Nat,
                Equal(Call("g", Ids("H", "a", "b", "k")),
                Call("gcd", Seq(Call("F", Seq(F.Id("k"), Plus, D(3))), Cdot, Sp, F.Id("a"), Plus,
                    Call("F", Seq(F.Id("k"), Plus, D(4))), Cdot, Sp, F.Id("b")), F.Id("H"))))),
                "The source coordinates a,b and the modulus H are natural numbers.",
                DescribeRole.Definition),
            Node("primitive", "Prime-primitive signed state", Disp(All(F.Id("p"), Nat,
                All(Vars("n", "z"), Int, Seq(Call("Primitive", Ids("p", "n", "z")),
                Sp, Leftrightarrow, Sp, Par(Seq(Neg, Call("dvd", F.Id("p"), Call("abs", F.Id("n"))),
                    Sp, Lor, Sp, Neg, Call("dvd", F.Id("p"), Call("abs", F.Id("z"))))))))),
                "A state is p-primitive when at least one coordinate is not divisible by p.",
                DescribeRole.Definition),
            Paragraph(Text("For each prime p, write r=zeroRank(p), the least positive d with p dividing F(d). "
                + "For a finite positive-time table S, let A be its phase image modulo r. "
                + "Set T=r-1 when r=p+1 and T=r otherwise.")),
            Node("prime_phase_gcd_sampling", "Sharp identification and fixed-source late separation",
                Disp(ResultFormula()),
                "The two identification statements include zero and nonprimitive states, hence constant "
                + "saturated readings. Only the number of distinct queried phases matters; no answer at "
                + "time zero or common content is supplied. The rank satisfies 3<=r<=p+1, and "
                + "pairwise recovery gives distinct kernel directions. A unit scalar return preserves zero "
                + "support, without "
                + "requiring the Fibonacci step to return to the identity. Nonzero states have at most "
                + "one zero phase. When r=p+1 every direction has one; otherwise an affine direction "
                + "avoids all zero phases. Missing one phase in the proper case, or two in the full case, "
                + "therefore gives indistinguishable primitive states. Their inverse-source residues "
                + "(5n-3z,-3n+2z), scaled by Q, lie strictly below Qp and realize every positive-time "
                + "reading simultaneously. Both states and both sources are fixed before the cutoff B. "
                + "The later separating time alone varies. The local p,1 separation uses unscaled "
                + "signed states even when p divides Q. Natural-source identification is modulo p, "
                + "not a claimed general-modulus Qp identification criterion.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create("prime-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula[] Ids(params string[] names) => names.Select(F.Id).ToArray();
    private static Formula Vars(params string[] names) => Seq([.. names.SelectMany((name, index) =>
        index == 0 ? new[] { F.Id(name) } : new[] { Comma, Sp, F.Id(name) })]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(params Formula[] values) => Seq([.. values.SelectMany((value, index) =>
        index == 0 ? new[] { Par(value) } : new[] { Sp, Land, Sp, Par(value) })]);
    private static Formula All(Formula names, Formula domain, Formula body) =>
        Seq(Forall, Sp, names, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula names, Formula domain, Formula body) =>
        Seq(Exists, Sp, names, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula Iff(Formula left, Formula right) =>
        Seq(Par(left), Sp, Leftrightarrow, Sp, Par(right));
    private static Formula Positive(Formula value) => Seq(D(0), Lt, value);
    private static Formula LtThan(Formula left, Formula right) => Seq(left, Lt, right);

    private static Formula Recovery(bool natural)
    {
        Formula p = F.Id("p"), k = F.Id("k");
        string first = natural ? "a" : "n", second = natural ? "b" : "z";
        string reading = natural ? "g" : "G";
        Formula answers = Equal(Call(reading, p, F.Id(first), F.Id(second), k),
            Call(reading, p, F.Id(first + "Prime"), F.Id(second + "Prime"), k));
        return All(Vars(first, second, first + "Prime", second + "Prime"), natural ? Nat : Int,
            Imp(All(k, F.Id("S"), answers), All(k, Nat, Imp(Positive(k), answers))));
    }

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p"), S = F.Id("S"), k = F.Id("k"), Q = F.Id("Q"), t = F.Id("t");
        Formula rank = Call("zeroRank", p);
        Formula phases = Call("image", Seq(k, Sp, Mapsto, Sp, Call("mod", k, rank)), S);
        Formula phaseThreshold = Call("if", Equal(rank, Seq(p, Plus, D(1))),
            Seq(rank, Minus, D(1)), rank);
        Formula H = Seq(Q, Cdot, Sp, p), B = F.Id("B"), count = Call("card", phases);
        Formula n = F.Id("n"), z = F.Id("z"), n2 = F.Id("nPrime"), z2 = F.Id("zPrime");
        Formula a = F.Id("a"), b = F.Id("b"), a2 = F.Id("aPrime"), b2 = F.Id("bPrime");
        Formula signedEquality = Equal(Call("G", p, n, z, k), Call("G", p, n2, z2, k));
        Formula sourceEquality = Equal(Call("g", H, a, b, k), Call("g", H, a2, b2, k));
        Formula transport = All(k, Nat, Imp(Positive(k), And(
            Equal(Call("g", H, a, b, k), Seq(Q, Cdot, Sp, Call("G", p, n, z, k))),
            Equal(Call("g", H, a2, b2, k), Seq(Q, Cdot, Sp, Call("G", p, n2, z2, k))))));
        Formula agreement = All(k, S, And(signedEquality, sourceEquality));
        Formula late = All(B, Nat, Some(t, Nat, And(LtThan(B, t), Positive(t),
            Seq(Neg, Par(Seq(t, Sp, InMacro, Sp, S))), Equal(Call("G", p, n, z, t), p),
            Equal(Call("G", p, n2, z2, t), D(1)), Equal(Call("g", H, a, b, t), H),
            Equal(Call("g", H, a2, b2, t), Q),
            Equal(Call("g", H, a2, b2, t), Call("div", H, p)))));
        Formula witnesses = Some(Vars("n", "z", "nPrime", "zPrime"), Int,
            Some(Vars("a", "b", "aPrime", "bPrime"), Nat, And(
                Call("Primitive", p, n, z), Call("Primitive", p, n2, z2),
                LtThan(a, H), LtThan(b, H), LtThan(a2, H), LtThan(b2, H), transport, agreement, late)));
        Formula threshold = Seq(phaseThreshold, Le, count);
        Formula result = And(Iff(Recovery(false), threshold), Iff(Recovery(true), threshold),
            Imp(LtThan(count, phaseThreshold), All(Q, Nat, Imp(Positive(Q), witnesses))));
        return All(p, Nat, Imp(Call("Prime", p), All(S, Call("Finset", Nat),
            Imp(All(k, S, Positive(k)), result))));
    }
}
