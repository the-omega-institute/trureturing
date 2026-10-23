using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class HellingerEnergyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/androulakis2023nussbaumszkola");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singular logarithmic energy bound for arbitrary noncommuting quantum states.",
        H("Hellinger energy and the trace norm"), Blocks(
            Generic("resolution_diagonal","The actual spectral diagonal", "For every full actual resolution d of a positive trace-class contraction T and every vector v, the real series d(i)*norm(inner(v,d(i))) squared has the actual quadratic form Re inner(v,T v) as its sum. Square-root CFC eigenvector action and Parseval give genuine real summability. No trace normalization or finite entropy is required."),
            Generic("resolution_entropy","Entropy in every full resolution", "For every full actual resolution d of T, the nonnegative extended sum of -d(i) log(d(i)) equals spectralEntropy T. The generic spectral-energy identity and self energy prove the equality, including zero fibers and infinite entropy. No trace normalization is required."),
            Generic("resolution_cross_energy","The full extended cross double series", "For arbitrary full resolutions d of rho and e of sigma, the double sum (ofReal(d(i))*singularLog(e(j)))*ofReal(norm(inner(e(j),d(i))) squared) equals spectralEnergy sigma rho. The diagonal identity followed by nonnegative double summation proves it. This identity retains arbitrary index sets, full zero eigenspaces, zero times infinity and infinite cross energy, without normalization or finite-energy assumptions. It supplies both the Hellinger bound and the finite signed logarithmic formula."),
            Describe.Lean(DescribeId.Create("quantum-hellinger-energy"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.spectralEntropy_add_traceNorm_sq_le_energy"),
                H("Entropy with a quantitative trace-norm reward"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let H be any complete complex Hilbert space. The arguments rho and sigma are positive trace-class contractions with actual real trace one. The norm is the Banach trace norm on TraceClass H. Their native full spectral resolutions have arbitrary Set indices and retain every zero eigenvector. No separability, finite dimension, faithfulness, commutation or finite entropy is assumed.")),
                    Paragraph(Text("For eigenvalues r,s in [0,1], the scalar inequality eta(r)+r+(sqrt(r)-sqrt(s)) squared <= r ell(s)+s follows from log(t)<=t-1 with t=sqrt(s)/sqrt(r). Here eta(0)=0 and ell(0)=infinity. If r=0 the equality is s=s; if r>0 and s=0 the right side is infinite. Zero times infinity remains zero.")),
                    Paragraph(Text("For full native bases u and v, the transition weights c(i,j)=norm(inner(v(j),u(i))) squared have row and column sum one by unconditional Parseval. Square-root functional calculus acts on each eigenvector. Self-adjointness and Parseval identify the actual diagonal of rho at v(j) with the genuinely summable series sum r(i)c(i,j), and identify the square-root difference coordinates with (sqrt(r(i))-sqrt(s(j)))inner(v(j),u(i)).")),
                    Paragraph(Text("The square roots are Hilbert-Schmidt because the original positive operators are trace class; their difference is Hilbert-Schmidt as well. Converting genuine real square sums to ENNReal and applying nonnegative double summation gives S(rho)+1+ofReal(HSdifferenceSquare)<=E_sigma(rho)+1. Only the finite trace-one addend is canceled. Infinite entropy, infinite cross energy and singular zero fibers are preserved.")),
                    Paragraph(Text("The noncommuting identity rho-sigma=R(R-S)+(R-S)S, where R=sqrt(rho) and S=sqrt(sigma), combines with the Hilbert-Schmidt product trace-norm estimate and the triangle inequality. Both square roots have square sum one in the same full basis, so norm(rho-sigma)<=2 sqrt(HSdifferenceSquare). This yields the displayed reward. Dropping its nonnegative term gives the Gibbs inequality. The full weighted entropy theorem applies the stronger bound to both states relative to their actual mixture.")),
                    Paragraph(Text("The spectral distribution viewpoint is the established Nussbaum-Szkola correspondence. Mathlib supplies functional calculus, Parseval and unconditional sums. The analytic trace-class and ideal estimates are the existing attributed Physlib suppliers; their provenance and licenses are unchanged. This bound does not prove entropy continuity, compactness of a state family, or existence of a common full-space Hamiltonian."))), DescribeRole.Theorem))));
    private static DocumentBlock Generic(string name,string title,string text)=>Describe.Lean(
        DescribeId.Create("quantum-hellinger-"+name.Replace('_','-')),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy."+name),
        H(title),StatementSource.FromAuthor(Call(name.Replace("_",""),F.Id("FullSpectralResolutions"))),
        AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula Statement()
    {
        Formula h=F.Id("H"), r=F.Id("rho"), s=F.Id("sigma");
        Formula ent=Call("spectralEntropy",r);
        Formula reward=Call("ofReal",Call("divide",Call("square",Call("traceNorm",Call("subtract",r,s))),D(4)));
        Formula body=new Formula.Relation(Call("add",ent,reward),FormulaRelationOperator.LessThanOrEqual,Call("spectralEnergy",s,r));
        Formula hyp=new Formula.Logic(Call("PositiveTraceOne",r),FormulaLogicOperator.And,Call("PositiveTraceOne",s));
        return new Formula.BindMany(FormulaQuantifier.ForAll,[
            new(FormulaIdentifier.Create("H"),F.Id("CompleteComplexHilbertSpace")),
            new(FormulaIdentifier.Create("rho"),Call("Reference",h)),
            new(FormulaIdentifier.Create("sigma"),Call("Reference",h))],
            new Formula.Logic(hyp,FormulaLogicOperator.Implies,body));
    }
}
