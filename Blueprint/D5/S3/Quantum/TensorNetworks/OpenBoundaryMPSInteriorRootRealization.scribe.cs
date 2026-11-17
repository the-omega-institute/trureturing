using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorRootRealizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A distinct common determinant root gives an actual finite uniform bond-two state with identical entire raw interior Q2 and a different full-state phase class; annular boundary and real transversality hypotheses give such a root conditionally.",
        H("From residual roots to actual interior ambiguity"), Blocks(
            Definition("Sector", "The fixed sector", "A sector contains three arbitrary complex numbers lambda, mu and a. All trial operations keep this sector fixed."),
            Definition("delta", "Eigenvalue difference", "delta=mu-lambda."),
            Definition("alpha", "First sector offset", "alpha=lambda-a."),
            Definition("beta", "Second sector offset", "beta=mu-a."),
            Definition("Regular", "Regular sector", "Regular means delta times alpha times beta is nonzero and normSq(1+conjugate(lambda) mu) is strictly positive. These are algebraic nonvanishing conditions, not positivity of an inverse."),
            Definition("B", "Diagonal sector matrix", "B=diag(lambda,mu)."),
            Definition("G", "Trial core matrix", "G(z) has rows (1,z) and (alpha,beta z). Its determinant is delta z."),
            Definition("C", "The fixed intertwining matrix", "C has rows (a,1) and (-alpha beta,lambda+mu-a). The exact identity C G(z)=G(z) B holds."),
            Definition("core", "Uniform binary core", "The two matrices are A0=G(z), A1=B G(z), at every site."),
            Definition("K", "Fixed central pair factors", "In word order 00,01,10,11 the matrices are I,C,B,BC, and A_i A_j=K_ij G(z)^2."),
            Definition("diagonalInverse", "Algebraic diagonal inverse", "Entry (i,j) is divided by 1+b_i conjugate(b_j), where b=(lambda,mu). Regularity makes every divisor nonzero."),
            Definition("diagonalStarInverse", "Algebraic adjoint diagonal inverse", "Entry (i,j) is divided by 1+conjugate(b_i)b_j. Its order in inverseDualTransfer is essential."),
            Definition("inverseTransfer", "Inverse transfer in its actual order", "E_z inverse sends H to G(z) inverse times diagonalInverse(H) times G(z) inverse-adjoint. Both composition identities are proved. This algebraic inverse is not asserted to preserve positivity."),
            Definition("inverseDualTransfer", "Inverse dual transfer in its actual order", "EStar_z inverse sends P to diagonalStarInverse(G(z) inverse-adjoint P G(z) inverse). Congruence occurs before the Schur inverse. Both composition identities are proved."),
            Definition("leftTarget", "Fixed actual left environment", "P=(EStar_z0)^p(l dagger l), for the original arbitrary actual left boundary l."),
            Definition("rightTarget", "Fixed actual right environment", "H=G(z0)^2 E_z0^q(r r dagger) (G(z0)^2) dagger. The central G square is included on both sides."),
            Definition("trialLeft", "Trial left boundary Gram", "X_p(zeta)=(inverseDualTransfer_zeta)^p(P), with P fixed."),
            Definition("trialRight", "Trial right boundary Gram", "Y_q(zeta)=(inverseTransfer_zeta)^q(G(zeta) inverse-square H G(zeta) inverse-adjoint-square), with H fixed."),
            Definition("residual", "The explicit real residual", "f(zeta)=Re(det X_p(zeta))+I Re(det Y_q(zeta)). The map is real rather than holomorphic. Target P,H are fixed in all trial derivatives."),
            Theorem("iterate_smul", "Homogeneous iteration", IterateSmul(),
                "Every complex-homogeneous map on Bond remains complex-homogeneous under every natural iterate, including zero. The original root-realization factorization and InteriorPolynomial's live right-boundary and Jacobian-scaling proofs directly consume this original helper."),
            Theorem("transfer_smul", "Homogeneous transfer", TransferSmul(),
                "For every binary pair of Bond matrices, every complex scalar and every Bond matrix, transfer commutes with scalar multiplication. The original root proof and InteriorPolynomial's actual right-target scaling use this declaration directly through iterate_smul; no positivity or nonzero-scalar hypothesis is added."),
            Theorem("distinct_residual_root_actual_ambiguity", "Every distinct common root is actual", Endpoint(false),
                "For every p,q at least one, every regular sector, nonzero original z0, arbitrary complex l,r and positive definite actual P,H, any nonzero zeta distinct from z0 with both trial determinants zero gives a nonzero actual finite uniform bond-two competitor. It has identical complete unnormalized rawInterior p 2 q, at length (p+2)+q, and is not any unit complex scalar times the original full state. No canonical-chart or regularity hypothesis is imposed on the constructed boundaries."),
            Theorem("annular_regular_root_actual_ambiguity", "Conditional annular actual ambiguity", Endpoint(true),
                "Retain the same universal finite p,q and actual target hypotheses. Let 0<epsilon<norm(z0)<R. Assume the first residual component is strictly negative on both boundary circles and the ordinary real Frechet derivative at z0 is an invertible continuous real linear map L. Then the same actual nonzero nonphase competitor exists. Continuity of this explicit residual on the closed annulus, the original-root identity f(z0)=0, Hermitian preservation and actual root realization are proved, not assumed."),
            Paragraph(Text("The reused CommonCore dictionary gives the entire raw observation, with actual append(append(left,block),right) and total length (p+2)+q. With prefix rows L_u=l A_u and right columns S_v=G(z)^2 A_v r, one has P=L dagger L, H=S S dagger, and Q2(w,wprime)=trace(P K_w H K_wprime dagger). This identity retains all sixteen complex entries and the affine scale. The prefix rank-at-most-two Schur record is not used.")),
            Paragraph(Text("At a common root the trial matrices are Hermitian and have determinant zero. The existing rank-one factor supplier factors each nonzero trial matrix. Hermitian symmetry makes its scalar multiple of an outer Gram real. Forward transfer and dual transfer preserve positive semidefiniteness. A nonpositive scalar would make the forward image nonpositive, contradicting a strictly positive diagonal entry of the positive definite target. Its positive square root supplies actual finite left and right boundaries. The inverse identities recover P,H exactly; no positive inverse is assumed.")),
            Paragraph(Text("For phase separation the fixed matrices I,C,B,BC span all complex two by two matrices. Positive target Grams supply explicit left and right inverses. A hypothetical phase equality therefore gives U M V=eta M for every matrix M. Nonzero eta makes U,V invertible; U commutes with every matrix and the existing scalar-center theorem gives U=h I, h nonzero. Thus the two actual prefix row families are proportional. Sampling words zero to the power p-1 followed by j gives the invertible column systems Ralpha and Rbeta, with determinants alpha delta and beta delta, forcing zeta=z0. The argument uses the actual arbitrary boundaries, not an old canonical chart.")),
            Paragraph(Text("The annular result directly consumes AnnularSecondZero.annular_second_zero. That supplier uses TauCeti.not_contractibleSpace_sphere, source revision 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported with its Apache-2.0 attribution and retained license at docs/reports/licenses/tauceti-sphere-port-LICENSE.txt. The imported C8 reconstruction remains attributed to Haobo Ma and Wenlin Zhang, Proof of Critch-Morton Conjecture 8, CC BY 4.0. Neither reused result is new root-realization mathematics.")),
            Paragraph(Text("This is a conditional root-to-actual result, not C9 or a genericity theorem, and earns zero solved-open-problem credit. General endpoint operator limits and determinant signs, universal all-length transversality, finite canonical-chart coverage and dominance, and genericity on the actual state and actual raw-density images remain separate obligations. No normalization, holomorphicity, strict derivative, regularity of other zeros, nonzero winding, clock, dynamics, positive physical inverse, stability or thermodynamic cost is asserted.")))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("interior-root-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula f, string prose) =>
        Describe.Lean(DescribeId.Create("interior-root-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula IterateSmul()
    {
        var f = Id("F"); var t = Id("t"); var x = Id("X"); var n = Id("n");
        var homogeneous = Bind([("t", Id("Complex")), ("X", Id("Bond"))],
            Eq(new Formula.Apply(f, [Call("smul", t, x)]), Call("smul", t, new Formula.Apply(f, [x]))));
        return All("F", Arrow(Id("Bond"), Id("Bond")), Imp(homogeneous,
            Bind([("n", Id("Nat")), ("t", Id("Complex")), ("X", Id("Bond"))],
                Eq(Call("iterate", f, n, Call("smul", t, x)), Call("smul", t, Call("iterate", f, n, x))))));
    }
    private static Formula TransferSmul()
    {
        var a = Id("A"); var t = Id("t"); var x = Id("X");
        return Bind([("A", Arrow(Call("Fin", D(2)), Id("Bond"))),
            ("t", Id("Complex")), ("X", Id("Bond"))],
            Eq(Call("transfer", a, Call("smul", t, x)), Call("smul", t, Call("transfer", a, x))));
    }
    private static Formula Endpoint(bool annular)
    {
        var p = Id("p"); var q = Id("q"); var s = Id("s"); var z = Id("z");
        var zo = Id("zo"); var l = Id("l"); var r = Id("r"); var phi = Id("phi");
        var eta = Id("eta"); var eps = Id("epsilon"); var radius = Id("R"); var derivative = Id("L");
        var n = Add(Add(p, D(2)), q);
        var boundary = Arrow(Call("Fin", D(2)), Id("Complex"));
        var stateType = Arrow(Call("Word", n), Id("Complex"));
        var psi = Call("mpsState", n, Call("core", s, zo, D(0)), Call("core", s, zo, D(1)), l, r);
        var P = Call("leftTarget", s, zo, l, p); var Henv = Call("rightTarget", s, zo, r, q);
        var f = Call("residual", s, p, q, P, Henv);
        var phase = Some("eta", Id("Complex"), And(Eq(Call("norm", eta), D(1)), Eq(phi, Call("smul", eta, psi))));
        var result = Some("phi", stateType, And(Call("SetMember", phi, Call("openBoundaryMPS", n)),
            Ne(phi, D(0)), Eq(Call("rawInterior", p, D(2), q, phi), Call("rawInterior", p, D(2), q, psi)),
            Seq(Neg, Sp, Par(phase))));
        Formula last;
        if (annular)
        {
            var circle = All("z", Id("Complex"), Imp(Or(Eq(Call("norm", z), eps), Eq(Call("norm", z), radius)),
                Lt(Call("re", new Formula.Apply(f, [z])), D(0))));
            last = Bind([("epsilon", Id("Real")), ("R", Id("Real")),
                ("L", Call("ContinuousLinearEquiv", Id("Real"), Id("Complex"), Id("Complex")))],
                Imp(And(Lt(D(0), eps), Lt(eps, Call("norm", zo)), Lt(Call("norm", zo), radius),
                    Call("HasFDerivAt", f, Call("toContinuousLinearMap", derivative), zo), circle), result));
        }
        else
        {
            last = All("z", Id("Complex"), Imp(And(Ne(z, D(0)), Ne(z, zo),
                Eq(Call("det", Call("trialLeft", s, p, P, z)), D(0)),
                Eq(Call("det", Call("trialRight", s, q, Henv, z)), D(0))), result));
        }
        return Bind([("p", Id("Nat")), ("q", Id("Nat")), ("s", Id("Sector")),
            ("zo", Id("Complex")), ("l", boundary), ("r", boundary)],
            Imp(And(Le(D(1), p), Le(D(1), q), Call("Regular", s), Ne(zo, D(0)),
                Call("PosDef", P), Call("PosDef", Henv)), last));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b)
    {
        for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b);
        return b;
    }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
