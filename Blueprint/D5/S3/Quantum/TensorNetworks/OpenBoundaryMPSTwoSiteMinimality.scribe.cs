using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSTwoSiteMinimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-site raw prefix ambiguity on a nonempty canonical chart", H("Two-site prefix minimality on the canonical parameter chart"),
        Blocks(
            Item("parameters", "Parameter", "Thirteen real parameter coordinates",
                "The source is (Fin 5 to complex) times real times complex. Its coordinates are x,p,q,u,v,rho,r1. The left row is (x,1), the right column is (rho,r1), and the real positive condition on rho fixes only unit complex phase. It retains positive amplitude scale on the raw affine cone.", DescribeRole.Definition),
            Item("core", "core", "The canonical symbol matrices",
                "The two matrices have first rows (p,q) and (u,v), and second rows (1-xp,-xq) and (-xu,1-xv). Their products with the left row are exactly the two standard physical rows. The source model is the existing openBoundaryMPS model with independent free boundaries.", DescribeRole.Definition),
            Item("record", "densityRecord", "The twelve real raw density coordinates",
                "Using the fixed ordering 00,01 then 10,11, retain the two real diagonal entries of the leading block H, its complex off-diagonal entry, and the complex two by two upper-right block B. This defines a twelve-real-dimensional vector space. The record map is evaluated on the actual rawPrefix density of the canonical MPS state; all its coordinates are real C-infinity.", DescribeRole.Definition),
            Item("three-site-phase-rigidity", "three_site_phase_rigidity", "Phase rigidity at three sites",
                "For positive real rho and rho-prime, equality of two canonical three-site tensors up to a unit complex phase forces equality of every parameter, provided the second tensor lies in the supplied coherent chart. Compare the two applications of the original triple_gauge: the normalized physical rows force the two gauge matrices to agree, and the second coordinate of the left row fixes their scalar discrepancy. The right boundary is recovered by summing l_i l_j t_ijk. The resulting positive real boundary comparison eliminates unit phase. This inverse argument is attributed to Haobo Ma and Wenlin Zhang's CC BY 4.0 note Proof of Critch-Morton Conjecture 8 and its existing Lean supplier, rather than claimed as new C9 mathematics. The all-length theorem below applies the original outside_sum_exact at the prefix, with induced boundary (A0+A1)^m r.", DescribeRole.Theorem),
            Item("density-record-injective", "densityRecord_injective", "Schur completion from the fixed record",
                "Two Hermitian matrices on two-bit words with rank at most two are equal when their twelve-coordinate records agree and the fixed leading principal block of the first matrix is invertible. Hermitian symmetry recovers the leading block from its diagonal real parts and one complex entry. Normalize the top block of the matrix operator by an explicit input shear. The linear vertical-rank criterion kills its lower-right Schur complement, proving D equals B-dagger H-inverse B. The result includes singular matrices of rank below two in its hypotheses, although invertibility of H forces the rank to equal two. The actual-density application uses the original columns_factor: the amplitude columns factor through a two-dimensional bond, their Gram is Hermitian, and its rank is at most two.", DescribeRole.Theorem),
            Item("canonical-chart", "canonicalChart", "The full intended phase-fixed chart",
                "At source length 3+m, require positive real rho, nonvanishing of chartPoly on the actual coherent first-three-site improper marginal, nonzero determinant of A0+A1, and nonzero determinant of the fixed Q2 leading principal block. The Q2 complement length is 1+m. Every condition refers to the actual canonical state map. The intended original problem has m at least one. The explicit uniform witness below proves nonemptiness for every natural m, in particular for every source length at least four.", DescribeRole.Definition),
            Item("open-canonical-chart", "isOpen_canonicalChart", "Openness in the actual real source",
                "The full canonicalChart is open in the thirteen-dimensional real parameter space. The coherent marginal is a finite sum of actual amplitudes, all entries of the state and raw density are real smooth, and evaluation of chartPoly and the two determinants are continuous. This is an openness theorem for the parameter chart; it does not assert openness or density of its image among actual states or in a phase quotient.", DescribeRole.Theorem),
            Item("record-collision", "record_collision", "Actual parameter collisions in every open set",
                "For every complement length m and every specified nonempty open subset of the actual thirteen-real-dimensional canonical parameter space, two distinct parameters have the same twelve raw Q2 record coordinates. The proof compiles the actual smooth MPS observation map and consumes the real C1 dimension obstruction. The open_subchart_collision theorem supplies the additional density and phase bridges. Neither parameter theorem establishes genericity or phase saturation in the full actual state image.", DescribeRole.Theorem),
            Item("all-length-phase-rigidity", "phase_rigidity", "All-length unit-phase rigidity",
                "For every natural m, two parameters in canonicalChart m that give phase-equal actual states at length 3+m are equal. Sum the coherent complement of length m using the original outside_sum_exact. Apply the Ma-Zhang canonical three-site inverse with the induced right boundary, recover that boundary by contraction, and cancel the invertible power of S=A0+A1. The positive real first coordinate of each original right boundary forces the unit phase to be one. No equivalence under arbitrary nonzero complex scaling is used.", DescribeRole.Theorem),
            Item("open-subchart-collision", "open_subchart_collision", "Full raw Q2 collisions between different phase classes",
                "For every m and every specified nonempty open U contained in canonicalChart m, there exist two actual free-boundary MPS states in the image of U with equal entire rawPrefix 2 (1+m) and no unit phase relating them. The C1 dimension obstruction is applied to the actual smooth twelve-real record map on the thirteen-real parameter source. The original amplitude-column factorization gives a Hermitian Gram of rank at most two; fixed-H Schur completion turns record equality into equality of all raw Q2 entries. All-length phase rigidity then turns distinct parameters into distinct phase classes. The existential witnesses remain in the actual matrix-and-boundary image. This is a local parameter-open no-fewer theorem. It does not assert a dense intrinsic real-algebraic state locus or phase saturation of arbitrary open state loci, and does not alone resolve Conjecture 9.", DescribeRole.Theorem),
            Item("nonempty-canonical-chart", "canonicalChart_nonempty", "A uniform full-length witness",
                "For every natural m, canonicalChart m is nonempty. Start from A0=[[1,2],[3,4]], A1=[[5,6],[7,8]], l=(1,0), r=(1,2). The exact full-length gauge U=[[1,2],[5,6]], s=1/2 gives canonical l=(-3,1), A0=[[1,1/2],[4,3/2]], A1=[[-1/2,2],[-3/2,7]] and right boundary 2^(2+m)(5,17), preserving every amplitude at length 3+m. The original positive sum matrix keeps the coherent right boundary (x,y) strictly positive. Direct kernel-checked Cramer and chart-factor identities have only nonzero factors x+y and 5x+8y on this positive cone. The canonical sum determinant is -2. For the Q2 complement 1+m, the first tail Gram is the Gram of columns (5,11) and (17,23), whose determinant is -72. An invertible A0 preserves positive definiteness under further transfers. The fixed prefix rows (7,10) and (19,22) have determinant -36, so the fixed leading density block is positive definite at every length. Gauge preservation transfers its invertibility to the canonical witness. No transfer-operator determinant is identified with det(A0+A1).", DescribeRole.Theorem))));

    private static DocumentBlock Item(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula()
                : StatementSource.FromAuthor(Disp(Statement(name))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Complex => Seq(Mathbb, Grp(X("C")));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula At(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] fs) => fs.Aggregate((a, b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Member(Formula x, Formula s) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Parameter => At("Parameter");
    private static Formula Rho(Formula x) => At("fst", At("snd", x));

    private static Formula Statement(string name)
    {
        if (name == "three_site_phase_rigidity")
        {
            var theta = X("theta"); var eta = X("eta"); var zeta = X("zeta");
            return All("theta", Parameter, All("eta", Parameter,
                Imp(Less(D(0), Rho(theta)), Imp(Less(D(0), Rho(eta)),
                    All("zeta", Complex, Imp(Eqn(At("norm", zeta), D(1)),
                        Imp(Eqn(At("state", D(3), eta), At("smul", zeta, At("state", D(3), theta))),
                            Imp(new Formula.Not(Eqn(At("eval", At("state", D(3), eta), At("chartPoly")), D(0))),
                                Eqn(theta, eta)))))))));
        }
        if (name == "densityRecord_injective")
        {
            var matrix = At("Matrix", At("Word", D(2)), At("Word", D(2)), Complex);
            var p = X("Q"); var q = X("P");
            var conclusion = Imp(Eqn(At("densityRecord", p), At("densityRecord", q)), Eqn(p, q));
            conclusion = Imp(At("IsUnit", At("det", At("leading", p))), conclusion);
            conclusion = Imp(Le(At("rank", q), D(2)), conclusion);
            conclusion = Imp(Le(At("rank", p), D(2)), conclusion);
            conclusion = Imp(At("IsHermitian", q), conclusion);
            conclusion = Imp(At("IsHermitian", p), conclusion);
            return All("Q", matrix, All("P", matrix, conclusion));
        }
        if (name == "phase_rigidity")
        {
            var m = X("m"); var theta = X("theta"); var eta = X("eta"); var zeta = X("zeta");
            var length = At("add", D(3), m);
            var conclusion = Imp(Eqn(At("state", length, eta), At("smul", zeta, At("state", length, theta))), Eqn(theta, eta));
            conclusion = All("zeta", Complex, Imp(Eqn(At("norm", zeta), D(1)), conclusion));
            conclusion = Imp(Member(eta, At("canonicalChart", m)), conclusion);
            conclusion = Imp(Member(theta, At("canonicalChart", m)), conclusion);
            return All("m", Nat, All("theta", Parameter, All("eta", Parameter, conclusion)));
        }
        if (name == "canonicalChart_nonempty")
            return All("m", Nat, At("Nonempty", At("canonicalChart", X("m"))));
        if (name == "open_subchart_collision")
        {
            var m = X("m"); var u = X("U"); var psi = X("psi"); var phi = X("phi"); var zeta = X("zeta");
            var complement = At("add", D(1), m); var length = At("add", D(2), complement);
            var stateType = At("Function", At("Word", length), Complex);
            var image = At("image", At("state", length), u);
            var phase = Some("zeta", Complex, And(Eqn(At("norm", zeta), D(1)), Eqn(phi, At("smul", zeta, psi))));
            var pairs = And(Member(psi, At("openBoundaryMPS", length)), Member(phi, At("openBoundaryMPS", length)),
                Eqn(At("rawPrefix", D(2), complement, psi), At("rawPrefix", D(2), complement, phi)), new Formula.Not(phase));
            var result = Some("psi", stateType, And(Member(psi, image), Some("phi", stateType, And(Member(phi, image), pairs))));
            return All("m", Nat, All("U", At("Set", Parameter), Imp(At("IsOpen", u), Imp(At("Nonempty", u),
                Imp(At("subset", u, At("canonicalChart", m)), result)))));
        }
        if (name == "isOpen_canonicalChart")
            return All("m", Nat, At("IsOpen", At("canonicalChart", X("m"))));
        var collision = And(Member(X("eta"), X("U")),
            new Formula.Not(Eqn(X("theta"), X("eta"))),
            Eqn(At("record", X("m"), X("theta")), At("record", X("m"), X("eta"))));
        var witnesses = Some("theta", Parameter, And(Member(X("theta"), X("U")),
            Some("eta", Parameter, collision)));
        return All("m", Nat, All("U", At("Set", Parameter),
            Imp(At("IsOpen", X("U")), Imp(At("Nonempty", X("U")), witnesses))));
    }
}
