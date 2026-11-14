using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSTwoSiteMinimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical real MPS parameters and a finite prefix record", H("Toward two-site prefix minimality"),
        Blocks(
            Item("parameters", "Parameter", "Thirteen real parameter coordinates",
                "The source is (Fin 5 to complex) times real times complex. Its coordinates are x,p,q,u,v,rho,r1. The left row is (x,1), the right column is (rho,r1), and the real positive condition on rho fixes only unit complex phase. It retains positive amplitude scale on the raw affine cone.", DescribeRole.Definition),
            Item("core", "core", "The canonical symbol matrices",
                "The two matrices have first rows (p,q) and (u,v), and second rows (1-xp,-xq) and (-xu,1-xv). Their products with the left row are exactly the two standard physical rows. The source model is the existing openBoundaryMPS model with independent free boundaries.", DescribeRole.Definition),
            Item("record", "densityRecord", "The twelve real raw density coordinates",
                "Using the fixed ordering 00,01 then 10,11, retain the two real diagonal entries of the leading block H, its complex off-diagonal entry, and the complex two by two upper-right block B. This defines a twelve-real-dimensional vector space. The record map is evaluated on the actual rawPrefix density of the canonical MPS state; all its coordinates are real C-infinity.", DescribeRole.Definition),
            Item("three-site-phase-rigidity", "three_site_phase_rigidity", "Phase rigidity at three sites",
                "For positive real rho and rho-prime, equality of two canonical three-site tensors up to a unit complex phase forces equality of every parameter, provided the second tensor lies in the supplied coherent chart. Compare the two applications of the original triple_gauge: the normalized physical rows force the two gauge matrices to agree, and the second coordinate of the left row fixes their scalar discrepancy. The right boundary is recovered by summing l_i l_j t_ijk. The resulting positive real boundary comparison eliminates unit phase. This inverse argument is attributed to Ma-Zhang's note.tex and the existing Conjecture 8 supplier, rather than claimed as new C9 mathematics. Extension through an arbitrary-length coherent prefix is a separate obligation.", DescribeRole.Theorem),
            Item("density-record-injective", "densityRecord_injective", "Schur completion from the fixed record",
                "Two Hermitian matrices on two-bit words with rank at most two are equal when their twelve-coordinate records agree and the fixed leading principal block of the first matrix is invertible. Hermitian symmetry recovers the leading block from its diagonal real parts and one complex entry. Normalize the top block of the matrix operator by an explicit input shear. The linear vertical-rank criterion kills its lower-right Schur complement, proving D equals B-dagger H-inverse B. The result includes singular matrices of rank below two in its hypotheses, although invertibility of H forces the rank to equal two. Applying this result to actual MPS densities still requires their factorization and rank bound; the theorem does not assume those missing bridges have been supplied.", DescribeRole.Theorem),
            Item("canonical-chart", "canonicalChart", "The full intended phase-fixed chart",
                "At source length 3+m, require positive real rho, nonvanishing of chartPoly on the actual coherent first-three-site improper marginal, nonzero determinant of A0+A1, and nonzero determinant of the fixed Q2 leading principal block. The Q2 complement length is 1+m. Every condition refers to the actual canonical state map. The intended original problem has m at least one. Nonemptiness for every such m is a separate unproved obligation.", DescribeRole.Definition),
            Item("open-canonical-chart", "isOpen_canonicalChart", "Openness in the actual real source",
                "The full canonicalChart is open in the thirteen-dimensional real parameter space. The coherent marginal is a finite sum of actual amplitudes, all entries of the state and raw density are real smooth, and evaluation of chartPoly and the two determinants are continuous. This is an openness theorem for the parameter chart; it does not assert openness or density of its image among actual states or in a phase quotient.", DescribeRole.Theorem),
            Item("record-collision", "record_collision", "Actual parameter collisions in every open set",
                "For every complement length m and every specified nonempty open subset of the actual thirteen-real-dimensional canonical parameter space, two distinct parameters have the same twelve raw Q2 record coordinates. The proof compiles the actual smooth MPS observation map and consumes the real C1 dimension obstruction. This does not on its own assert equality of full Q2, distinct phase classes, nonemptiness of the required canonical chart at every length, or resolution of Conjecture 9.", DescribeRole.Theorem))));

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
