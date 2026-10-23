using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaCosetFiberLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaCosetFiberLift.";
    private static readonly Formula N = F.Id("N"), n = F.Id("n"), K = F.Id("K"),
        c = F.Id("c"), u = F.Id("u"), v = F.Id("v"), B = F.Id("B"),
        C = F.Id("C"), Hh = F.Id("H"), L = F.Id("L"), e = F.Id("e"), d = F.Id("d");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cp => Seq(C, Apos);
    private static Formula NE => Seq(N, Ell);
    private static Formula PiN => Seq(Pi, Underscore, Grp(N, Comma, Ell));
    private static Formula Units(Formula a) => Seq(Open, Seq(Mathbb, Grp(F.Id("Z"))), Slash,
        a, Seq(Mathbb, Grp(F.Id("Z"))), Close, Caret, Grp(Times));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Sep(args), Close);
    private static Formula Sep(Formula[] args) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(args, (a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })));
    private static Formula Inv(Formula a) => Seq(a, Caret, Grp(Minus, D(1)));
    private static Formula Count(Formula a) => Seq(Lvert, Sp, a, Rvert);
    private static Formula R(Formula a, Formula x) => Seq(F.Id("r"), Underscore, Grp(a), Open, x, Close);
    private static Formula M(Formula a, Formula x) => Seq(F.Id("M"), Underscore, Grp(a), Open, x, Close);
    private static Formula Dev(Formula a, Formula k, Formula x) =>
        Seq(F.Id("F"), Underscore, Grp(a), Open, k, Comma, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, x, Colon, type, Close, Comma, Sp, body);
    private static Formula Bracket(string type, Formula arg) =>
        Seq(OpenBracket, Call(type, arg), CloseBracket, Sp);
    private static Formula Coset(Formula modulus, Formula k, Formula x) =>
        Call("cosetFinset", modulus, k, x);
    private static Formula Lift(Formula x) => Call("liftedFinset", N, Ell, x);

    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo();

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Reduction of a unit coset through a coprime prime extension of the modulus "
                + "has an exact rational least-residue first moment. Two finite bijections "
                + "identify retained units and removed prime multiples on native unit groups.",
            H("Uniform Least-Residue Unit-Coset Lift"),
            Blocks(
                Paragraph(Text("For every modulus n, the unit group is the actual group "
                    + "of invertible elements of Z/nZ, and r denotes the natural-valued ZMod.val. "
                    + "At positive moduli this is the least nonnegative representative. "
                    + "At n greater than one every unit has representative "
                    + "between one and n minus one. Cardinalities are finite carrier cardinalities. "
                    + "All moment and deviation arithmetic below is rational; the integer "
                    + "representative is coerced before subtraction.")),
                Node("coset", "Actual finite left cosets", "cosetFinset", Provenance,
                    Disp(All(n, Nat, Seq(Bracket("NeZero", n),
                        All(K, Call("Subgroup", Units(n)), All(c, Units(n),
                            Seq(Coset(n, K, c), Sp, Eq, Sp, OpenBrace, Sp, u, Sp,
                                InMacro, Sp, Units(n), Sp, Mid, Sp, Inv(c), u, Sp,
                                InMacro, Sp, K, CloseBrace)))))),
                    "The membership condition is c inverse times u in K, so this is the left coset cK.",
                    DescribeRole.Definition),
                Node("reduction", "Reduction on the actual unit groups", "reduceUnits", Provenance,
                    Disp(All(N, Nat, All(Ell, Nat,
                        Seq(Call("reduceUnits", N, Ell), Sp, Eq, Sp,
                            Call("unitsMap", Seq(N, Sp, Mid, Sp, NE)))))),
                    "This multiplicative map is induced by reduction modulo N, using N dividing N ell. "
                        + "Its source is the unit group modulo N ell and its target the unit group modulo N.",
                    DescribeRole.Definition),
                Node("preimage", "The actual reduction preimage", "liftedFinset", Provenance,
                    Disp(All(N, Nat, All(Ell, Nat, Seq(Bracket("NeZero", NE),
                        All(B, Call("Finset", Units(N)), Seq(Lift(B), Sp, Eq, Sp,
                            OpenBrace, Sp, v, Sp, InMacro, Sp, Units(NE), Sp, Mid, Sp,
                            Call("reduceUnits", N, Ell), Open, v, Close, Sp,
                            InMacro, Sp, B, CloseBrace)))))),
                    "The lifted finite set contains exactly the units whose reduction belongs to the given set.",
                    DescribeRole.Definition),
                Node("moment", "The rational least-residue moment", "moment", Provenance,
                    Disp(All(n, Nat, All(B, Call("Finset", Units(n)),
                        Seq(M(n, B), Sp, Eq, Sp, Sum, Underscore,
                            Grp(u, Sp, InMacro, Sp, B), Sp, R(n, u), Sp, InMacro, Sp, Q)))),
                    "Each integer representative is coerced into the rationals before summing.",
                    DescribeRole.Definition),
                Node("deviation", "The subgroup-sized rational center", "deviation", Provenance,
                    Disp(All(n, Nat, All(K, Call("Subgroup", Units(n)),
                        All(B, Call("Finset", Units(n)),
                            Seq(Dev(n, K, B), Sp, Eq, Sp, M(n, B), Minus,
                                Frac, Grp(n, Count(K)), Grp(D(2))))))),
                    "The center uses the cardinality of the subgroup, while the finite set is an explicit argument.",
                    DescribeRole.Definition),
                Node("result", "The complete uniform lift theorem", "result", Provenance,
                    ResultFormula(), ProofText, DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        Formula count = Seq(Count(K), Open, Ell, Minus, D(1), Close);
        Formula hypotheses = Seq(D(1), Sp, Lt, Sp, N, Sp, Land, Sp,
            Call("Prime", Ell), Sp, Land, Sp, Call("Coprime", Ell, N));
        Formula statement = Seq(
            Count(Hh), Sp, Eq, Sp, count, Sp, Land, RowBreak, Grp(),
            Count(L), Sp, Eq, Sp, count, Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, d, Sp, InMacro, Sp, Units(NE), Comma, Sp,
                PiN, Open, d, Close, Sp, Eq, Sp, c, Sp, Land, Sp,
                L, Sp, Eq, Sp, Coset(NE, Hh, d), Close, Sp, Land, RowBreak, Grp(),
            M(NE, L), Sp, Eq, Sp, Ell, Sp, M(N, C), Plus,
                Frac, Grp(N, Count(K), Ell, Open, Ell, Minus, D(1), Close), Grp(D(2)),
                Minus, Ell, Sp, M(N, Cp), Sp, Land, RowBreak, Grp(),
            Dev(NE, Hh, L), Sp, Eq, Sp, Ell, Open, Dev(N, K, C), Minus,
                Dev(N, K, Cp), Close, Sp, Land, RowBreak, Grp(),
            Dev(NE, Hh, L), Sp, Eq, Sp, Ell, Open, M(N, C), Minus, M(N, Cp), Close);
        Formula body = Let(PiN, Call("reduceUnits", N, Ell),
            Let(Hh, Seq(Inv(PiN), Open, K, Close),
                Let(e, Call("unitOfCoprime", Ell),
                    Let(C, Coset(N, K, c),
                        Let(Cp, Coset(N, K, Seq(Inv(e), c)),
                            Let(L, Lift(C), statement))))));
        return Disp(All(N, Nat, All(Ell, Nat,
            All(K, Call("Subgroup", Units(N)), All(c, Units(N),
                Seq(hypotheses, Sp, Rightarrow, RowBreak, Grp(), body))))));
    }

    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, variable, Sp, Eq, Sp, value, Sp,
            Operatorname, Grp(F.Id("in")), Sp, body);

    private static DocumentBlock Node(string id, string title, string declaration,
        AssessedProvenance provenance, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("unit-coset-lift-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), Provenance,
            Blocks(Paragraph(Text(prose))), role);

    private const string ProofText =
        "Index all representative blocks by (u,t) in C times {0,...,ell minus one}, "
        + "with q equal to r_N(u) plus Nt. The representative bound gives q below N ell, "
        + "and reduction of q modulo N is u. Consequently q is coprime to N. "
        + "Euclidean quotient and remainder recover the pair, proving uniqueness. "
        + "For blocks not divisible by ell, q is coprime to both factors and defines "
        + "a unit modulo N ell reducing to u. Conversely a lifted unit v gives "
        + "(pi(v),r_(N ell)(v)/N). Its reduction representative is the remainder modulo N, "
        + "so the division equation recovers q exactly. Unit coprimality excludes "
        + "divisibility by ell. The two maps are mutually inverse on native unit carriers "
        + "and preserve the representative weight. "
        + "For removed blocks, a unit y in C prime gives z equal to ell times r_N(y). "
        + "The unit ey belongs to C, its representative is z modulo N, and the block "
        + "(ey,z/N) has value z. In the inverse direction, divisibility gives "
        + "a equal to q/ell with ell a equal to q and a below N. Coprimality of q "
        + "with N implies coprimality of a with N, so a defines a native unit y. "
        + "Reducing ell a equal to q proves ey equal to u; hence y belongs to "
        + "the inverse-translated coset C prime. Division and block uniqueness prove "
        + "both inverse identities. The removed weight is exactly ell times r_N(y). "
        + "Summing all blocks gives ell M_N(C) plus N times the size of C times "
        + "ell(ell minus one)/2, with the triangular sum calculated in the rationals. "
        + "The removed sum is ell M_N(C prime), while the retained sum is M_(N ell)(L). "
        + "Their disjoint partition proves the first-moment formula. Multiplication "
        + "identifies each coset with K, so there are |K|ell blocks and |K| removed "
        + "blocks. Thus L has |K|(ell minus one) elements. Setting c equal to one "
        + "identifies its lift with H. Surjectivity of reduction on units provides "
        + "d reducing to c, and pi(v) in cK is equivalent to d inverse times v in H, "
        + "proving L equal to dH. Finally subtract the proven lifted center from "
        + "the first-moment formula. The small-modulus centers are equal and cancel. "
        + "No step uses primality of N, oddness of ell, a proper subgroup, an identity "
        + "coset or cyclicity. Literature priority remains unassessed; no novelty "
        + "claim is made.";
}
