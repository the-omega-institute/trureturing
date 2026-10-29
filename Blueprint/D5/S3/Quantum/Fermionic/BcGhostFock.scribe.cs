using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostFockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostFock.";
    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname); tokens.Add(Grp(F.Id(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }
    private static Formula A(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula E(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Negate(Formula x) => new Formula.Negate(x);
    private static Formula Int => V("Int");
    private static Formula B(Formula m) => C("b", m);
    private static Formula G(Formula m) => C("c", m);
    private static Formula Omega => V("vacuum");
    private static Formula Zero => D(0);
    private static Formula One => Seq(Open, D(1), Colon, C("Module.End", V("Complex"), V("Fock")), Close);
    private static Formula Pair(Formula x, Formula y) => Add(Mul(x, y), Mul(y, x));
    private static Formula Ite(Formula condition, Formula yes, Formula no) => C("ite", condition, yes, no);
    private static Formula NatPart(Formula x) => C("Int.toNat", x);
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("bc-ghost-fock-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        var m = V("m"); var n = V("n"); var j = V("j"); var ji = C("Int.ofNat", j);
        var bCreator = C("create", Mul(D(2), NatPart(Sub(Negate(m), D(2)))));
        var bAnnihilator = C("annihilate", Add(Mul(D(2), NatPart(Add(m, D(1)))), D(1)));
        var bdef = Ite(Le(m, Negate(D(2))), bCreator, bAnnihilator);
        var cdef = Ite(Le(n, D(1)), C("create", Add(Mul(D(2), NatPart(Sub(D(1), n))), D(1))), C("annihilate", Mul(D(2), NatPart(Sub(n, D(2))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "All integer bc ghost modes act on the algebraic countable finite-excitation carrier with the exact mixed delta, vacuum cuts, odd parity, a one-dimensional common annihilator kernel and scalar commutant.",
            H("Integer bc ghost CAR"), Blocks(
                Paragraph(Text("Fock, its signed creators and annihilators, vacuum and parity are those of CountableOccupationFock. Even sites encode the b-creator and c-annihilator pair; odd sites encode the c-creator and b-annihilator pair. Int.toNat is applied to a nonnegative expression in every active branch. CAR is transferred from the original finite Jordan–Wigner matrices through the proved occupation intertwinings and exact finite capture, then consumed by the exhaustive integer branch calculation.")),
                Node("b", A("m", Int, Eqn(B(m), bdef)), "The creation branch ends at m equal to minus two; the annihilation branch starts at minus one.", DescribeRole.Definition),
                Node("c", A("n", Int, Eqn(G(n), cdef)), "The creation branch ends at n equal to one; the annihilation branch starts at two.", DescribeRole.Definition),
                Node("mode_correspondence", A("j", V("Nat"), And(Eqn(B(Sub(Negate(ji), D(2))), C("create", Mul(D(2), j))), And(Eqn(G(Add(ji, D(2))), C("annihilate", Mul(D(2), j))), And(Eqn(G(Sub(D(1), ji)), C("create", Add(Mul(D(2), j), D(1)))), Eqn(B(Sub(ji, D(1))), C("annihilate", Add(Mul(D(2), j), D(1)))))))), "These four inverse formulas cover every natural occupation index and establish the zero-mode convention."),
                Node("ghost_b_car", A("m", Int, A("n", Int, Eqn(Pair(B(m), B(n)), Zero))), "Same-species b modes anticommute. Cross-branch occupation indices have distinct parity."),
                Node("ghost_c_car", A("m", Int, A("n", Int, Eqn(Pair(G(m), G(n)), Zero))), "Same-species c modes anticommute for the same exhaustive branch reason."),
                Node("ghost_mixed_car", A("m", Int, A("n", Int, Eqn(Pair(B(m), G(n)), Ite(Eqn(Add(m, n), Zero), One, Zero)))), "Only an even creator with its even annihilator, or an odd annihilator with its odd creator, contributes. In either case equality of occupation indices is equivalent to m plus n equal to zero. In particular the mixed zero-mode anticommutator is the identity."),
                Node("ghost_vacuum", And(A("m", Int, Imp(Le(Negate(D(1)), m), Eqn(C("b", m, Omega), Zero))), And(A("n", Int, Imp(Le(D(2), n), Eqn(C("c", n, Omega), Zero))), And(Eqn(C("c", D(1), Omega), C("ket", C("Finset.singleton", D(1)))), And(Eqn(C("c", Zero, Omega), C("ket", C("Finset.singleton", D(3)))), And(Ne(C("c", D(1), Omega), Zero), Ne(C("c", Zero, Omega), Zero)))))), "The annihilation cuts are exact. The states c one vacuum and c zero vacuum are the distinct nonzero singleton occupations one and three."),
                Node("ghost_parity", A("m", Int, And(Eqn(Pair(V("parity"), B(m)), Zero), Eqn(Pair(V("parity"), G(m)), Zero))), "Both ghost families are odd for the actual occupation parity involution."),
                Node("ghost_common_annihilator_kernel", A("v", V("Fock"), Iff(And(A("m", Int, Imp(Le(Negate(D(1)), m), Eqn(C("b", m, V("v")), Zero))), A("n", Int, Imp(Le(D(2), n), Eqn(C("c", n, V("v")), Zero)))), E("alpha", V("Complex"), Eqn(V("v"), Smul(V("alpha"), Omega))))), "The c annihilation branch enumerates every even source index and the b annihilation branch every odd source index. The inverse formulas in mode_correspondence reduce the two complete integer cuts to the actual common annihilator kernel. The reverse inclusion uses both cuts of ghost_vacuum."),
                Node("scalar_commutant", A("A", C("Module.End", V("Complex"), V("Fock")), Imp(A("m", Int, Eqn(Mul(V("A"), B(m)), Mul(B(m), V("A")))), Imp(A("n", Int, Eqn(Mul(V("A"), G(n)), Mul(G(n), V("A")))), E("alpha", V("Complex"), Eqn(V("A"), Smul(V("alpha"), One)))))), "For an arbitrary complex linear endomorphism commuting with all integer b and c, the exact vacuum cuts show that A vacuum lies in the joint ghost annihilator kernel, hence equals alpha times vacuum. The two creator branches of mode_correspondence give commutation with every actual source creator. Creator-word induction and the full countable creator_spanning theorem then prove A equals alpha times the identity on the entire carrier. No continuity, assumed irreducibility, positivity or finite-cutoff restriction is used."),
                Paragraph(Text("This is the algebraic CAR and vacuum representation. It does not assert positive ghost unitarity, nonnegative ghost energy or uniqueness of a degree-zero vacuum. The common annihilator vacuum line and scalar commutant do not imply those spectral statements. Pointwise finite odd normal sums, primary commutators, integer degree and the evaluated minus twenty-six anomaly remain further obligations. An all-state super vertex algebra, the intended matter and graded tensor realization, the actual BRST charge, its domain and normal constant, nilpotence and cohomology, no-ghost and Monster–Lorentz identifications, fusion, sewing, CFT, string and AdS conclusions require their own proofs.")))));
    }
}
