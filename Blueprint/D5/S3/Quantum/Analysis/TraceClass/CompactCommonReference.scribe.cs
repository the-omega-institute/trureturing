using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class CompactCommonReferenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual continuous spectral-energy reference on a compact convex state family.",
        H("Entropy centers and one common reference"), Blocks(
            Item("spectralEnergy_le_entropy_of_isMaxOn", "A convex entropy center controls cross energy", Center(),
                "Let C be any real-convex family in the genuine trace-class Banach space of a complete complex Hilbert space. Every member is an actual positive operator with real trace one and finite spectral entropy. Let gamma be an actual Reference belonging to C and maximizing realEntropy on C. Compactness is not a premise of this center theorem.",
                "For rho in C and 0<t<1, form the actual normalized mixture tau=(1-t)gamma+t rho. Nonnegative rho-slot linearity and self energy identify (1-t)E_tau(gamma)+t E_tau(rho) with S(tau). The actual Gibbs inequality is the consequence of spectralEntropy_add_traceNorm_sq_le_energy obtained by discarding its nonnegative reward. It gives S(gamma)<=E_tau(gamma), while maximality gives S(tau)<=S(gamma).",
                "Rewrite the finite S(gamma) as (1-t)S(gamma)+t S(gamma). Cancel the finite first summand and the strictly positive finite coefficient t in ENNReal. Thus E_tau(rho)<=S(gamma). Along t=1/(n+2), the actual trace-class mixture converges to gamma in trace norm. Reference-slot lower semicontinuity passes the bound to E_gamma(rho). Singular zero eigenspaces and noncommuting references remain in scope."),
            Item("fullCompactCommonReference", "A single reference in the actual compact family", Endpoint(),
                "Let A be a nonempty compact real-convex set of actual positive trace-one trace-class operators. Assume its actual spectral entropy is finite and realEntropy is continuous on A. The result constructs an actual entropy maximizer gamma in A and one actual Reference sigma whose underlying trace-class operator belongs to A. For that same sigma, genuine spectralEnergy is finite and continuous on A in both ENNReal and real value, and is everywhere at most realEntropy(gamma)+log(2).",
                "Compact attainment constructs the global maximizer. For every scale eta=2^(-m), uniform entropy continuity supplies a positive radius r with 2r below the continuity modulus. A finite open ball cover with centers in A gives nonempty closed convex cells A intersect closedBall(c,r). Genuine compact attainment supplies every local entropy center. The center theorem controls its cross energy on its entire cell. The open ball is a neighborhood relative to A, including at endpoints of a convex family.",
                "Average the finitely many local centers at scale m to a_m in A. With c_m=(1/4)(1/2)^m, define sigma=(1/2)gamma+sum_m c_m a_m in the genuine trace-class Banach space. Norm-one states and the geometric series give trace-norm summability. The normalized residual partial sums (1-sum_(m<N)c_m)gamma+sum_(m<N)c_m a_m all belong to A and converge to sigma. Compact closedness proves sigma belongs to A. The actual closed positive cone after operatorCLM passes finite-sum order to the limit, giving gamma/2<=sigma and (c_m/N_m)gamma_mj<=sigma.",
                "Global reference antitonicity, scaling and the global center bound give E_sigma(rho)<=S(gamma)+log(2), hence finiteness. No cover-cardinality growth estimate is used. The local weight w=c_m/N_m may be arbitrarily small.",
                "For the local center gamma' and P=w gamma'<=sigma, orderedEnergy P sigma is lower semicontinuous in rho. On the closed cell, scaling and positive decomposition give E_gamma'(rho)-log(w)=orderedEnergy(P,sigma,rho)+E_sigma(rho), with both terms finite. The finite logarithmic constant cancels exactly between nearby states. The local entropy oscillation, Gibbs at the base state and lower semicontinuity of the ordered increment bound the upper energy jump. The real-value lower-cut argument treats negative cuts by nonnegativity, including the zero-increment branch. All neighborhoods are relative to A.",
                "Rho-slot spectral-energy lower semicontinuity comes from the shared lowerSemicontinuousOn_spectralEnergy_state theorem in EnergySublevelCompactness, on the full cone of actual positive trace-class operators. Composition with a continuous positive-valued map restricts this theorem to the family A. Combining its finite real-value version with the upper estimate gives real continuity, then ENNReal continuity through ofReal. This is a repository synthesis of the existing genuine entropy and operator-energy APIs, not a literature novelty claim. Compactness remains an explicit input. The original Shirokov compactness-removal and full-space Hamiltonian conclusions are not asserted."))));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula.BoundVariable V(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula StateHyp(Formula a) => And(Call("AllPositiveTraceOne", a), Call("AllFiniteSpectralEntropy", a));
    private static Formula Center()
    {
        Formula h=F.Id("H"), c=F.Id("C"), g=F.Id("gamma"), r=F.Id("rho");
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [V("H",F.Id("CompleteComplexHilbertSpace")),V("C",Call("Set",Call("TraceClass",h))),V("gamma",Call("Reference",h)),V("rho",Call("TraceClass",h))],
            Implies(And(Call("RealConvex",c),And(StateHyp(c),And(Call("Member",g,c),And(Call("IsMaxOn",F.Id("realEntropy"),c,g),Call("Member",r,c))))),
                Le(Call("spectralEnergy",g,r),Call("spectralEntropy",g))));
    }
    private static Formula Endpoint()
    {
        Formula h=F.Id("H"), a=F.Id("A"), g=F.Id("gamma"), s=F.Id("sigma"), r=F.Id("rho");
        Formula bound=Call("add",Call("realEntropy",g),Call("log",D(2)));
        Formula energy=Call("spectralEnergy",s,r);
        Formula pointwise=new Formula.BindMany(FormulaQuantifier.ForAll,[V("rho",Call("TraceClass",h))],
            Implies(Call("Member",r,a),And(Call("Finite",energy),And(Le(energy,Call("ofReal",bound)),Le(Call("toReal",energy),bound)))));
        Formula conclusion=new Formula.BindMany(FormulaQuantifier.Exists,
            [V("gamma",Call("TraceClass",h)),V("sigma",Call("Reference",h))],
            And(Call("Member",g,a),And(Call("IsMaxOn",F.Id("realEntropy"),a,g),And(Call("Member",s,a),
                And(pointwise,And(Call("ContinuousOn",Call("spectralEnergy",s),a),Call("ContinuousOn",Call("RealSpectralEnergy",s),a)))))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,[V("H",F.Id("CompleteComplexHilbertSpace")),V("A",Call("Set",Call("TraceClass",h)))],
            Implies(And(Call("Nonempty",a),And(Call("IsCompact",a),And(Call("RealConvex",a),And(StateHyp(a),Call("ContinuousOn",F.Id("realEntropy"),a))))),conclusion));
    }
    private static DocumentBlock Item(string name,string title,Formula statement,params string[] texts) => Describe.Lean(
        DescribeId.Create("quantum-common-reference-"+name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference."+name),
        H(title),StatementSource.FromAuthor(statement),AssessedProvenance.FromRepo(),
        Blocks(texts.Select(t=>Paragraph(Text(t))).ToArray()),DescribeRole.Theorem);
}
