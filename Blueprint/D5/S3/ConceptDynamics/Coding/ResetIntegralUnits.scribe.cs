using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class ResetIntegralUnitsDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conj(params Formula[] c)
    {
        Formula f = c[^1];
        for (int j = c.Length - 2; j >= 0; --j) f = And(c[j], f);
        return f;
    }
    private static Formula Unique(string n, Formula t, Formula law, Formula otherLaw) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [B(n, t)], And(law,
            All(Imp(otherLaw, Equal(I("r"), I(n))), B("r", t))));
    private static DocumentBlock Entry(string n, string h, Formula f, string p, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(n.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/Coding/ResetIntegralUnits." + n), H(h),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(p))), role);

    private static Formula UnitRing => Call("Units", Call("QF", Num(2)));
    private static Formula Parameters => Call("product", I("Int"),
        Call("product", Call("Fin", Num(2)), Call("Fin", Num(2))));
    private static Formula Norm(Formula p) => Call("normal", Call("fst", p),
        Call("fst", Call("snd", p)), Call("snd", Call("snd", p)));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral compatibility yields every reset unit with unique signed time and two independent signs.",
        H("Coupled integral reset units"), Blocks(
            Paragraph(Text("Throughout this module q is exactly 2. QF(2) is the original quotient "
                + "Int[X]/(X^4-X^2-2X-1), Plus(2)=Int[X]/(X^2-X-1), and "
                + "Minus(2)=Int[X]/(X^2+X+1). ResetIntegralGluing supplies the faithful compatible-pair "
                + "reconstruction over the literal common coefficient-mod-two quotient. "
                + "All units and every signed integer time exponent are retained.")),
            Entry("quadratic_charts", "Literal quadratic charts and the four-element field",
                Conj(Call("IsField", Call("Common", Num(2))),
                    Equal(Call("card", Call("Common", Num(2))), Num(4)),
                    Equal(Call("golden", Call("root", Call("f", Num(2)))), I("phi")),
                    Equal(Call("eisenstein", Call("root", Call("g", Num(2)))), I("omega")),
                    Equal(Call("common", Call("root", Call("reduce", Call("g", Num(2))))), I("omega")),
                    All(Equal(Call("common", Call("rplus", Num(2), I("z"))),
                        Call("goldenReduce", Call("golden", I("z")))), B("z", Call("Plus", Num(2)))),
                    All(Equal(Call("common", Call("rminus", Num(2), I("z"))),
                        Call("modTwo", Call("eisenstein", I("z")))), B("z", Call("Minus", Num(2))))),
                "golden is the existing goldenAdjoinRootEquiv after equality of defining polynomials; "
                + "it fixes X to phi. eisenstein and common specialize the original "
                + "CalderonReciprocalMoments.coordinateEquiv at T=-1,N=1 over Int and ZMod 2. "
                + "Ideal.quotEquivOfEq transports the defining polynomial to X^2-C(-1)*X+C(1); "
                + "the supplier sends the root to omega=(0,1), and its inverse sends (a,b) to [a+bX]. "
                + "The supplier's rootToCoordinates is used directly for generator simplification. "
                + "Its generic telescope requires only a commutative coefficient ring, with no prime "
                + "or p-adic hypothesis. Each omega in the displayed formula has the coefficient "
                + "ring prescribed by its chart. Both reductions are literally (a,b) to "
                + "(a mod 2,b mod 2). The existing "
                + "inert_eisenstein_quotient_frobenius at ell=2 supplies maximality, the quotient field "
                + "and cardinal four, transported through these actual equivalences. "
                + "The reduction clauses are consumed in component_compatibility. This is a helper.",
                DescribeRole.Theorem),
            Entry("xUnit", "Forward time with a literal integral inverse",
                Call("hasType", I("xUnit"), UnitRing),
                "xUnit has value [X] and inverse [X^3-X-2]; multiplication gives one by the exact F "
                + "relation. wUnit has value [W], W=1+X+X^2-X^3, and inverse itself by the original "
                + "sign_square certificate. The component images of x,w,-1 are (phi,omega), "
                + "(1,-1), and (-1,-1), respectively. Negative time powers use this integral inverse.",
                DescribeRole.Definition),
            Entry("unit_normal_form", "Every unit has a unique full normal form",
                All(Unique("p", Parameters, Equal(I("u"), Norm(I("p"))),
                    Equal(I("u"), Norm(I("r")))), B("u", UnitRing)),
                "normal(n,a,b)=(-1)^a.val*wUnit^b.val*xUnit^n, with n:Int and a,b:Fin 2. "
                + "Use the existing golden_units_eq_signed_phi_pow for the plus component. Divide "
                + "by its scalar sign and signed time power. The normalized plus component is one, "
                + "so compatibility forces the minus component to reduce to one. At its original "
                + "EisensteinCohnReductionCore owner, unit_modTwo gives imaginary coefficient zero; "
                + "norm_unit_one then forces the real coefficient to be 1 or -1. Faithful integral "
                + "gluing reconstructs the normalized unit as 1 or wUnit. signedPhiPower_unique fixes "
                + "a,n, and the integral Eisenstein component distinguishes b=0 from b=1. "
                + "No six-unit classification is reproved; the two signs are independent.",
                DescribeRole.Theorem),
            Entry("unitsEquiv", "Oriented unit group equivalence",
                Call("hasType", I("unitsEquiv"), Call("GroupEquiv", UnitRing,
                    Call("product", Call("Multiplicative", I("Int")),
                        Call("product", Call("Multiplicative", Call("ZMod", Num(2))),
                            Call("Multiplicative", Call("ZMod", Num(2))))))),
                "parameterHom sends (n,a,b) to normal(n,a,b); unitsEquiv is the inverse of that "
                + "bijective group homomorphism. Parameter order is signed time, scalar sign, then "
                + "original Sign involution. The group law uses integer exponent addition and the "
                + "two square-one identities. Thus the inverse equivalence sends time 1 to xUnit, "
                + "the first sign to scalar -1, and the second sign to wUnit.",
                DescribeRole.Definition),
            Paragraph(Text("The new bridge is faithful integral reconstruction and its use to recover "
                + "an arbitrary unit from the reduction kernel. Component unit classifications and "
                + "chart transport are reused helpers. This is a repository synthesis with standard "
                + "quotient and quadratic-algebra APIs; no literature novelty is claimed. "
                + "ResetNativeUnitNormalForm consumes it on the original dimension group. The exact "
                + "original rho image and exclusion of scalar minus sign remain open.")))));

}
