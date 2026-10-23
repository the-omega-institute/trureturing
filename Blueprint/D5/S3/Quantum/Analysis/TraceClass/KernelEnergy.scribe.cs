using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class KernelEnergyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026operatorlog");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Kernel projection mass and singular logarithmic energy.",H("Zero spectral fibers and actual support"),Blocks(
            Item("kernelProjection_eigenvector","Actual projection action",Projection(),
                "kernelProjection(T) is the genuine bounded orthogonal projection onto the actual closed kernel of T. On a zero eigenvector it is identity. A nonzero eigenvector is perpendicular to the kernel: self-adjointness moves T across the inner product and its nonzero eigenvalue forces that inner product to vanish. The projection is therefore zero on every nonzero eigenfiber. This argument retains the whole zero eigenspace of a full native basis."),
            Item("kernelMass_hasSum","Actual zero-fiber trace mass",Mass(),
                "kernelMass(T,rho) is Re Tr(kernelProjection(T) rho). The product is trace class. The unconditional basis trace theorem and the continuous real-part map give genuine summability. Self-adjointness of the orthogonal projection moves it across each inner product; its actual eigenvector action identifies the diagonal with the original rho diagonal on zero fibers and zero elsewhere. Thus the displayed HasSum has the actual bounded projection trace as its value."),
            Item("spectralEnergy_eq_top_of_kernelMass_pos","Positive kernel mass forces infinity",Infinity(),
                "For positive trace-class rho, strictly positive actual kernel-projection mass implies some zero-fiber diagonal is positive. That term in the nonnegative singular spectral series is infinity, so the same spectralEnergy is infinity. A zero diagonal times the infinite logarithmic coefficient remains zero."),
            Item("ker_le_ker_of_spectralEnergy_lt_top","Finite energy forces actual kernel inclusion",Support(),
                "If spectralEnergy(T,rho) is finite, every zero-fiber rho diagonal must vanish. Positivity gives Re inner(v,rho v)=norm(sqrt(rho)v)^2. Hence rho annihilates every zero eigenvector. The operator rho kernelProjection(T) annihilates every vector of the full basis, so basis density makes it the zero continuous operator. The projection is identity on ker T, which proves ker T is contained in ker rho. The reverse implication is not asserted: support inclusion alone need not give finite energy."))));
    private static readonly Formula Hh=F.Id("H"),T=F.Id("T"),R=F.Id("rho"),W=F.Id("w"),B=F.Id("b"),S=F.Id("s");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula Ref=>Call("Reference",Hh);
    private static Formula Tc=>Call("TraceClass",Hh);
    private static Formula HAll(Formula.BoundVariable[] xs,Formula body)=>All([V("H",F.Id("CompleteComplexHilbertSpace")),..xs],body);
    private static Formula Spectral(Formula.BoundVariable[] xs,Formula body)=>HAll([V("T",Ref),V("w",Call("Set",Hh)),
        V("b",Call("HilbertBasis",W,F.Id("Complex"),Hh)),V("s",Call("Function",W,F.Id("Real"))),..xs],
        Implies(Call("EigenbasisEquation",T,B,S),body));
    private static Formula Projection()
    {
        Formula i=F.Id("i");
        return Spectral([V("i",W)],Equal(Call("apply",Call("kernelProjection",T),Call("apply",B,i)),
            Call("ifThenElse",Equal(Call("apply",S,i),D(0)),Call("apply",B,i),D(0))));
    }
    private static Formula Mass()=>Spectral([V("rho",Tc)],Call("HasSum",Call("zeroFiberDiagonal",B,S,R),Call("kernelMass",T,R)));
    private static Formula Infinity()=>HAll([V("T",Ref),V("rho",Tc)],
        Implies(And(Call("Nonnegative",R),Call("Positive",Call("kernelMass",T,R))),Equal(Call("spectralEnergy",T,R),F.Id("Infinity"))));
    private static Formula Support()=>HAll([V("T",Ref),V("rho",Tc)],
        Implies(And(Call("Nonnegative",R),Call("Finite",Call("spectralEnergy",T,R))),
            new Formula.Relation(Call("ker",Call("operator",T)),FormulaRelationOperator.LessThanOrEqual,Call("ker",Call("operator",R)))));
    private static DocumentBlock Item(string name,string title,Formula formula,string text)=>Describe.Lean(
        DescribeId.Create("kernel-"+name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/KernelEnergy."+name),H(title),StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula All(Formula.BoundVariable[] xs,Formula body)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],body);
}
