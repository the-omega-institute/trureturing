using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorSpectralAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical REAL13 spectral exclusion and actual ambiguity", H("Canonical spectral exclusion"), Blocks(
            Item("canonical_exclusion_actual_ambiguity", "Nonzero canonical certificate with actual raw interior ambiguity",
                "For each p,q at least one, P(p,q) is nonzero and for every canonical real x with sigma positive, P(p,q)(x) nonzero, and every e squared=D(coreCoordinates x), there exists a nonzero actual binary bond-two MPS of length N=(p+2)+q with exactly the same ENTIRE raw two-site interior as the canonical state with left L, cores A0,A1 and physical right sqrt(sigma)(1,eta), and no unit complex phase relation to that state. The proof consumes certificate_native, BOTH true native target PosDef conclusions, and the actual public nonzero_locus_actual_ambiguity through the conditional native endpoint and raw_amplitude. Native right is u^N S inverse times the original right. The outer G squared congruence remains outside the right transfer iterate. This canonical supplier is consumed by observed_interior_ambiguity in this same substantive spectral exclusion unit.", DescribeRole.Theorem),
            Item("observed_interior_ambiguity", "One observed polynomial for every interior two-site window",
                "Fix m at least one and N=3+m. In the existing 128 real prefix-Q3 coordinates Omega=(Word3 times Word3) plus itself, clear P(i+1,m-i) through the existing quotient numerator and denominator families to H_i/B_i, for i in Fin m. The literal polynomial is R_m=rho_m times the product of H_i. The product of the canonical P_i is nonzero. Real-polynomial density intersects the existing open nonempty quotientValidityDomain at one common x. Its positive representative is an ACTUAL length-N MPS; quotient retraction recovers x, all actual denominators and B_i are nonzero, and clearing makes every H_i nonzero there. Thus R_m has an actual nonzero evaluation, proves R_m nonzero, and supplies actual_principal_genericity exactly once. Its principal locus is nonempty, relatively open and dense in the ENTIRE literal openBoundaryMPS N subtype, and invariant under U(1). No claim about the Zariski closure is substituted.", DescribeRole.Theorem),
            Paragraph(Text("For EVERY target psi in this locus, EVERY p,q at least one with p+q=m+1, and EVERY length equality h:((p+2)+q)=3+m, there EXISTS a nonzero phi in the SAME actual image with rawInterior p 2 q (castState h phi)=rawInterior p 2 q (castState h psi), and no unit phase phi=eta times psi. The competitor can depend on the window and has no chart, Regular or locus restriction. In the displayed formula mk is the subtype constructor and amplitude variables use their underlying state functions. The proof obtains the target's positive quotient representative modulo a unit scalar, uses clearing to recover the appropriate P_i nonvanishing, chooses an actual complex square root with IsAlgClosed.exists_pow_nat_eq, and invokes canonical_exclusion_actual_ambiguity. Exact state-length casts and the same unit scalar transport the competitor; scalar cancellation preserves nonphase and nonzero. The live normg_nonzero proof supplies the finite product's nonvanishing through P_nonzero. Generic composition is proof organization, with no separate novelty claim.")),
            Paragraph(Text("The case m=1 is included: N=4 has the single interior pair p=q=1. This is pointwise ambiguity, not a competitor in every neighborhood, and not one competitor with all windows jointly equal. N=3 boundary-only composition, right reversal, one-site partial-trace adapters, full window composition and normalized readings remain obligations. Full C9 remains open and solved-open-problem KPI is zero.")))));
    private static DocumentBlock Item(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interiorspectralambiguity-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), name == "observed_interior_ambiguity"
                ? StatementSource.FromAuthor(Disp(ObservedFormula())) : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula ObservedFormula()
    {
        var m=Id("m"); var r=Id("R"); var psi=Id("psi"); var phi=Id("phi");
        var p=Id("p"); var q=Id("q"); var h=Id("h"); var z=Id("z"); var eta=Id("eta");
        var n=Add(D(3),m); var actual=Call("openBoundaryMPS",n);
        var locus=Call("actualPrincipalLocus",m,r); var zpsi=Call("smul",z,psi);
        var sameLocus=Iff(Call("Member",Call("mk",zpsi,Id("hz")),locus),Call("Member",psi,locus));
        var scalarMember=Some("hz",Call("Member",zpsi,actual),sameLocus);
        var saturation=All("psi",actual,All("z",Id("Complex"),
            Imp(Eq(Call("norm",z),D(1)),scalarMember)));
        var competitor=Some("phi",actual,And(Ne(phi,D(0)),
            Eq(Call("rawInterior",p,D(2),q,Call("castState",h,phi)),
               Call("rawInterior",p,D(2),q,Call("castState",h,psi))),
            Seq(Neg,Sp,Par(Some("eta",Id("Complex"),And(Eq(Call("norm",eta),D(1)),
                Eq(phi,Call("smul",eta,psi))))))));
        var windows=All("p",Id("Nat"),All("q",Id("Nat"),Imp(And(Le(D(1),p),Le(D(1),q),
            Eq(Add(p,q),Add(m,D(1)))),All("h",Eq(Add(Add(p,D(2)),q),n),competitor))));
        return All("m",Id("Nat"),Imp(Le(D(1),m),
            Some("R",Call("MvPolynomial",Call("Sum",Id("ObsIndex"),Id("ObsIndex")),Id("Real")),
                And(Ne(r,D(0)),Call("Nonempty",locus),Call("IsOpen",locus),Call("Dense",locus),
                    saturation,All("psi",actual,Imp(Call("Member",psi,locus),windows))))));
    }
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((a,b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Iff,Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);

}
