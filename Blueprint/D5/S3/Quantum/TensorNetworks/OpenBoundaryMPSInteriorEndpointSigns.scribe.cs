using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorEndpointSignsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    private static Formula C => Id("Complex");
    private static Formula Real => Id("Real");
    private static Formula Bond => Id("Bond");
    private static Formula S => Id("s");
    private static Formula P => Id("P");
    private static Formula Z => Id("z");
    private static Formula N => Id("p");
    private static Formula Dsq => Call("ofReal", Call("normSq", Call("delta", S)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full complex-linear operator norm limits of the native inverse dual transfer imply strict negative real residual values on both annular boundary circles for every regular sector and positive definite left target.",
        H("General regular-sector annular endpoint signs"), Blocks(
            Definition("Mzero", "Zero-endpoint matrix", "With v=(-alpha,1), Mzero is exactly diagonalStarInverse applied to vecMulVec(star v,v)."),
            Definition("Minf", "Infinity-endpoint matrix", "With u=(beta,-1), Minf is exactly diagonalStarInverse applied to vecMulVec(star u,u)."),
            Definition("inverseDualOperator", "The existing inverse as a complex-linear operator", "The underlying function is the existing inverseDualTransfer. The Bond norm is the elementwise supremum norm; the continuous-linear endomorphism space carries its genuine operator norm. No matrix multiplication normed-ring assumption is made."),
            Definition("zeroLimitOperator", "The zero limiting operator", "For every Bond X, zeroLimitOperator(s)(X)=(X11/d) smul Mzero, with d=normSq(delta). All scalar arithmetic in this displayed operator is complex, with the real d cast to Complex."),
            Definition("infinityLimitOperator", "The infinity limiting operator", "For every Bond X, infinityLimitOperator(s)(X)=(X00/d) smul Minf, with the same complex scalar convention."),
            Theorem("inverse_dual_operator_apply", "Exact native equality", Bind([("s", Id("Sector")), ("z", C), ("X", Bond)],
                Eq(Call("inverseDualOperator", S, Z, Id("X")), Call("inverseDualTransfer", S, Z, Id("X")))),
                "This equality is consumed in the scalar-power/native-iterate bridge. The native inverse, targets, residual and observation are reused unchanged."),
            Theorem("inverse_dual_operator_zero", "Operator norm convergence at punctured zero", OperatorLimit(true),
                "For every regular complex sector, norm(z)^2 times the bundled native inverse tends to zeroLimitOperator in the norm topology of Bond toL[Complex] Bond as z tends to zero through nonzero complex values."),
            Theorem("inverse_dual_operator_infinity", "Operator norm convergence at infinity", OperatorLimit(false),
                "For every regular complex sector, the bundled native inverse tends to infinityLimitOperator along the cobounded filter on Complex. This includes every complex direction and is not a radial or pointwise assertion."),
            Theorem("trial_left_zero", "Fixed native powers at punctured zero", TrialLimit(true),
                "For each fixed natural p at least one and arbitrary complex Bond P, norm(z)^(2p) times native trialLeft tends to P11 d^(-p) aone^(-(p-1)) smul Mzero, where aone=1+normSq(mu). No positivity is needed for this limit."),
            Theorem("trial_left_infinity", "Fixed native powers at infinity", TrialLimit(false),
                "For each fixed natural p at least one and arbitrary Bond P, native trialLeft tends to P00 d^(-p) (normSq(beta)/azero)^(p-1) smul Minf, where azero=1+normSq(lambda). There is no norm-growth assertion at infinity."),
            Theorem("annular_residual_negative", "Simultaneous circle-wide native residual signs", Annular(),
                "For every regular sector, every p at least one, every positive definite Bond P and every nonzero z0, the proof constructs 0<epsilon<norm(z0)<R. For every natural q, every Bond H and every complex z on either whole boundary circle, the real component of the existing residual is strictly negative. The radii are independent of q and H."),
            Paragraph(Text("Write U with rows (beta,-1),(0,0) and V with rows (0,0),(-alpha,1). For z nonzero the exact native inverse matrix is delta inverse smul (U+z inverse smul V). Congruence precedes diagonalStarInverse. The infinity extension is d inverse smul T((U+wV) dagger X (U+wV)); its composition with w=z inverse is the native operator. The zero extension is d inverse smul T(norm(z)^2 U dagger X U + conjugate(z) U dagger X V + z V dagger X U + V dagger X V). Exact equality with norm(z)^2 times the native operator holds throughout the punctured domain.")),
            Paragraph(Text("Entry continuity of the extension for every application is promoted by pinned Mathlib continuous_clm_apply using finite-dimensional Bond. This proves continuity into the actual endomorphism operator norm. Fixed powers of these same parameter-dependent operators converge by Tendsto.pow before evaluating at P. Composition is in native order; the exact scalar-power bridge gives the native iterates. The rank-one limiting operators are powered explicitly using Mzero11=1/aone and Minf00=normSq(beta)/azero.")),
            Paragraph(Text("Let c=normSq(1+conjugate(lambda) mu). The exact real determinant formulas are det(Mzero)=normSq(alpha)(1/(azero aone)-1/c) and det(Minf)=normSq(beta)(1/(azero aone)-1/c). The identity c=azero aone-d and Regular give c>0, d>0 and strictly negative determinants. Positive definiteness makes P00 and P11 real and positive; both fixed-power determinant limits are therefore strictly negative. At zero, det(t smul X)=t squared det(X) with t=norm(z)^(2p)>0 removes the scale. At infinity, the unscaled determinant tends to a negative constant. Neighborhood and cobounded-filter bases produce signs uniformly on circles enclosing the arbitrary z0.")),
            Paragraph(Text("This directly supplies the boundary-sign premise of annular_regular_root_actual_ambiguity. Full C9, real transversality, finite chart coverage, polynomial clearance and genericity in actual state and density images remain separate obligations. This unit earns zero solved external open problems. It introduces no dynamics, energy, physical clock, normalization, physical inverse or thermodynamic assertion.")))));

    private static Formula OperatorLimit(bool zero)
    {
        var family = zero ? LambdaOf("z", C, Call("smul", Call("ofReal", Pow(Call("norm", Z), D(2))), Call("inverseDualOperator", S, Z))) : Call("inverseDualOperator", S);
        return All("s", Id("Sector"), Imp(Call("Regular", S), Call("Tendsto", family,
            zero ? Call("puncturedNhds", D(0)) : Call("cobounded", C),
            Call("nhds", Call(zero ? "zeroLimitOperator" : "infinityLimitOperator", S)))));
    }
    private static Formula TrialLimit(bool zero)
    {
        var az = Call("ofReal", Add(D(1), Call("normSq", zero ? Call("mu", S) : Call("lambda", S))));
        var corner = Call("entry", P, zero ? D(1) : D(0), zero ? D(1) : D(0));
        var weight = zero ? Call("inv", az) : Call("div", Call("ofReal", Call("normSq", Call("beta", S))), az);
        var scalar = Mul(Mul(corner, Pow(Call("inv", Dsq), N)), Pow(weight, Sub(N, D(1))));
        var family = zero ? LambdaOf("z", C, Call("smul", Call("ofReal", Pow(Call("norm", Z), Mul(D(2), N))), Call("trialLeft", S, N, P, Z))) : Call("trialLeft", S, N, P);
        return Bind([("s", Id("Sector")), ("p", Id("Nat")), ("P", Bond)],
            Imp(And(Call("Regular", S), Le(D(1), N)), Call("Tendsto", family,
                zero ? Call("puncturedNhds", D(0)) : Call("cobounded", C),
                Call("nhds", Call("smul", scalar, Call(zero ? "Mzero" : "Minf", S))))));
    }
    private static Formula Annular()
    {
        var eps = Id("epsilon"); var radius = Id("R"); var zo = Id("zo");
        var circles = Bind([("q", Id("Nat")), ("H", Bond), ("z", C)],
            Imp(Or(Eq(Call("norm", Z), eps), Eq(Call("norm", Z), radius)),
                Lt(Call("re", Call("residual", S, N, Id("q"), P, Id("H"), Z)), D(0))));
        return Bind([("s", Id("Sector")), ("p", Id("Nat")), ("P", Bond), ("zo", C)],
            Imp(And(Call("Regular", S), Le(D(1), N), Call("PosDef", P), Ne(zo, D(0))),
                Some("epsilon", Real, Some("R", Real, And(Lt(D(0), eps), Lt(eps, Call("norm", zo)), Lt(Call("norm", zo), radius), circles)))));
    }
    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("interior-endpoint-" + name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("interior-endpoint-" + name.Replace('_', '-')), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b) { for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b); return b; }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Par(Seq(LambdaLower, Sp, Par(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, Par(body)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
