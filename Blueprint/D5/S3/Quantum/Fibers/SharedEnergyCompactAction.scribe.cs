using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class SharedEnergyCompactActionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Fibers/SharedEnergyCompactAction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual compact energy-group Haar averages retain precisely the complete total-energy blocks.",
        H("Compact Shared Energy Action"), Blocks(
            Def("energy-representation", "energyRepresentation", "The actual diagonal circle representation",
                "A circle phase z acts by the diagonal unitary with entries one, z and z to the power m. "
                    + "The integer energy labels give a continuous group homomorphism into the actual three-dimensional unitary matrices."),
            Def("energy-group", "energyGroup", "The actual compact matrix subgroup",
                "The energy group is the range subgroup of that continuous unitary representation. It is compact as the continuous image of the circle."),
            Def("energy-haar", "energyHaar", "Normalized Haar probability",
                "Haar measure on this actual compact matrix subgroup is normalized to total mass one."),
            Def("matrix-copies", "matrixCopies", "Native matrix tensor powers",
                "Matrix tensor powers use the same recursive basis as native density-state copies. The empty tensor power is the scalar identity."),
            Thm("energy-group-realization", "energy_group_realization", "Time evolution and its actual compact closure", EnergyGroupRealization(),
                "The matrices of the compact subgroup are precisely the closure of the time exponentials of the fixed Hamiltonian. "
                    + "Here the integer spectrum makes every circle phase an actual time value. Tensoring a time exponential gives "
                    + "the exponential of the sum Hamiltonian on the native tensor space, for every copy count."),
            Def("shared-moment", "sharedMoment", "Actual shared Haar tensor moments",
                "Each matrix coordinate is the Haar integral of the native tensor power of one conjugated density matrix. "
                    + "Every tensor factor uses the same matrix-group element. Finite-dimensional integration can be taken in these coordinates."),
            Thm("shared-haar-pinching", "shared_haar_pinching", "Actual Haar averaging equals complete total-energy pinching", HaarPinching(),
                "The actual compact-group Haar average equals complete total-energy pinching on every native density state. "
                    + "A tensor entry acquires the circle character of its total-energy difference. Equal energies give the constant "
                    + "character; for unequal energies a group translation negates the integrand, forcing its integral to vanish. "
                    + "All complex cross entries inside degenerate total-energy blocks remain."),
            Thm("moment-monomials", "moment_determines_monomials", "A moment determines all lower zero-weight monomials", MomentMonomials(),
                "Equality of one actual shared Haar moment implies equality of every labelled zero-weight coordinate monomial "
                    + "of no greater degree. Taking a native partial trace removes one copy: the equal head labels cancel in the energy condition, "
                    + "and their diagonal sum is one. Repeating this step and using the exponent-to-word construction gives the conclusion "
                    + "without dividing by any entry, including at degree zero and at deficient rank."),
            Def("same-energy-orbit", "SameEnergyOrbit", "Actual compact energy orbits",
                "Two native states have the same energy orbit when an actual matrix in the compact subgroup conjugates the first state matrix to the second."),
            Thm("compact-separation", "sparse_compact_separation", "Sparse compact-orbit separation by actual Haar moments", CompactSeparation(),
                "For every m at least two the literal sparse positive states belong to distinct actual compact orbits. "
                    + "Their shared Haar moments agree at every smaller copy count and differ at the stated count. "
                    + "Orbit conjugation preserves each complete total-energy pinching, so the explicit high-order tensor entry excludes orbit equivalence."),
            Thm("least-uniform-order", "least_uniform_order", "The exact least positive uniform copy order", LeastOrder(),
                "For every m at least two, twice m minus one is the least positive order at which equality of actual shared Haar moments "
                    + "is equivalent to membership in the same actual compact energy orbit, uniformly over every native three-dimensional density state. "
                    + "Every zero-weight exponent decomposes by strictly decreasing degree into labelled indecomposable exponents. "
                    + "Their degree bound and monomial multiplication extend one moment's equality to all zero-weight monomials. "
                    + "Hermitian coordinate pairs give equal moduli and identical zero supports. If the weight-one coordinate is nonzero, its phase ratio "
                    + "determines the common circle phase. If it vanishes, the remaining two nonzero coordinates have consecutive weights, "
                    + "so their zero-weight relation gives a common phase by a ratio. A single nonzero coordinate admits a circle root, "
                    + "and the empty support is immediate. These cases give an actual conjugating matrix, including deficient rank and m equal to two. "
                    + "Orbit conjugation gives the reverse implication at every order. The literal positive sparse pair excludes every smaller positive order."),
            Paragraph(Text("The explicit sparse effect gives no Helstrom optimum, adaptive protocol bound or postselection advantage.")))));
    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Length(Formula m) => Seq(D(2), Cdot, Sp, m, Minus, D(1));
    private static Formula TimeExponential(Formula m, Formula n, Formula t) =>
        C("exp", Seq(Open, Minus, C("imaginaryUnit"), Cdot, Sp, t, Close, Cdot, Sp, C("totalHamiltonian", m, n)));
    private static Formula EnergyGroupRealization()
    {
        var m = F.Id("m"); var n = F.Id("n"); var t = F.Id("t"); var u = F.Id("U");
        var groupRange = C("range", Seq(Open, LambdaLower, Sp, u, Colon, C("energyGroup", m), Comma, C("matrix", u), Close));
        var timeRange = C("range", Seq(Open, LambdaLower, Sp, t, Colon, C("Real"), Comma, TimeExponential(m, D(1), t), Close));
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma, RowBreak,
            groupRange, Eq, C("closure", timeRange), Sp, Land, RowBreak,
            Forall, Sp, n, InMacro, C("Nat"), Comma, Forall, Sp, t, InMacro, C("Real"), Comma,
            C("matrixCopies", TimeExponential(m, D(1), t), n), Eq, TimeExponential(m, n, t)));
    }
    private static Formula HaarPinching()
    {
        var m = F.Id("m"); var n = F.Id("n"); var r = F.Id("r");
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            Forall, Sp, r, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            C("sharedMoment", m, n, r), Eq, C("pinchedCopies", m, n, r)));
    }
    private static Formula CompactSeparation()
    {
        var m = F.Id("m"); var n = F.Id("n"); var l = C("copyOrder", m);
        var r = C("rho"); var s = C("sigma", m);
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp,
            Neg, Sp, C("SameEnergyOrbit", m, r, s), Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, C("Nat"), Comma, n, Lt, Length(m), Sp, Implies, Sp,
            C("sharedMoment", m, n, r), Eq, C("sharedMoment", m, n, s), Close, Sp, Land, RowBreak,
            C("sharedMoment", m, l, r), Neq, Sp, C("sharedMoment", m, l, s)));
    }
    private static Formula MomentMonomials()
    {
        var m = F.Id("m"); var n = F.Id("N"); var r = F.Id("r"); var s = F.Id("s"); var a = F.Id("a");
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            Forall, Sp, r, Comma, s, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            C("sharedMoment", m, n, r), Eq, C("sharedMoment", m, n, s), Sp, Implies, RowBreak,
            Forall, Sp, a, InMacro, C("Exponent"), Comma,
            C("degree", a), Leq, Sp, n, Sp, Implies, Sp,
            C("weight", m, a), Eq, D(0), Sp, Implies, Sp,
            C("monomial", C("stateMatrix", r), a), Eq, C("monomial", C("stateMatrix", s), a)));
    }

    private static Formula LeastOrder()
    {
        var m = F.Id("m"); var n = F.Id("N"); var r = F.Id("r"); var s = F.Id("s");
        var orders = Seq(OpenBrace, n, Colon, C("Nat"), Sp, Mid, Sp,
            D(0), Lt, n, Sp, Land, Sp,
            Forall, Sp, r, Comma, s, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            Open, C("sharedMoment", m, n, r), Eq, C("sharedMoment", m, n, s), Sp,
            Iff, Sp, C("SameEnergyOrbit", m, r, s), Close, CloseBrace);
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, C("IsLeast", orders, Length(m))));
    }

}
