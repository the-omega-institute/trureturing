using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class OrderedEnergyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026operatorlog");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noncommuting logarithmic increments and a positive extended energy identity.",
        H("Ordered logarithmic energy"), Blocks(
            Item("log_add_sub_log_eq_log_inverse", "A single-operator logarithmic difference", LogIdentity(),
                "For an actually strictly positive bounded operator A and c>=0, log(A+cI)-log(A)=log(I+c Ring.inverse(A)). The real spectrum of A is strictly positive. On that spectrum, the assertion is the scalar identity log(x+c)-log(x)=log(1+c/x). The CFC addition, inverse and composition theorems transfer this single-variable identity. All logarithm inputs have positive spectra. No product law for noncommuting operators is used, and c=0 is included."),
            Item("orderedIncrement_parameter_antitone", "Ordered increments increase at smaller epsilon", ParameterOrder(),
                "For 0<=P<=Q and 0<a<=b, define R_e=log(Q+eI)-log(P+eI). Logarithm monotonicity makes R_e nonnegative. With c=b-a, the single-operator difference formula identifies each shift difference with log(I+c Ring.inverse(T+aI)). Actual inverse order gives inverse(Q+aI)<=inverse(P+aI). Multiplication by c and operator logarithm monotonicity therefore order the shift differences. Rearranging yields R_b<=R_a, without assuming P and Q commute. Every shifted input is actually strictly positive."),
            Item("lowerSemicontinuous_orderedEnergy", "Trace-norm lower semicontinuity", Semicontinuity(),
                "orderedEnergy(P,Q,rho) is the ENNReal supremum of ofReal(Re Tr(R_epsilon_n rho)), with epsilon_n=1/(n+1). Each bounded observable pairs continuously with the actual trace-class Banach space. The supremum is lower semicontinuous in rho's trace norm. For ordered references and positive rho, these are actual nonnegative increasing expectations."),
            Item("spectralEnergy_eq_orderedEnergy_add", "Global singular energy decomposition", GlobalIdentity(),
                "For positive trace-class contraction references P<=Q and any positive trace-class rho, the SAME singular spectral energy satisfies E_P(rho)=F_(P,Q)(rho)+E_Q(rho) in ENNReal. The operator equality B_e(P)=R_e+B_e(Q) holds with the common positive regularization log(1+e)I-log(T+eI). Actual bounded trace additivity and positivity turn it into an ENNReal equality at each e. Both sequences increase on the same grid, so synchronized supremum addition gives the identity. It includes either or both singular energies being infinite and uses no subtraction of infinite values."),
            Item("orderedEnergy_self", "Equal singular references", EqualReferences(),
                "When P=Q, every actual increment is zero and F_(P,P)(rho)=0, even when E_P(rho) is infinite. Support inclusion alone supplies no finiteness conclusion. The decomposition is a supplier for common-reference continuity; local entropy-center construction and the final full-Hilbert-space Hamiltonian remain additional obligations."))));
    private static readonly Formula Hh=F.Id("H"),P=F.Id("P"),Q=F.Id("Q"),R=F.Id("rho");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula Ref=>Call("Reference",Hh);
    private static Formula Op=>Call("BoundedComplexOperator",Hh);
    private static Formula Tc=>Call("TraceClass",Hh);
    private static Formula HAll(Formula.BoundVariable[] xs,Formula body)=>All([V("H",F.Id("CompleteComplexHilbertSpace")),..xs],body);
    private static Formula LogIdentity()
    {
        Formula a=F.Id("A"),c=F.Id("c");
        return HAll([V("A",Op),V("c",F.Id("Real"))],Implies(And(Call("IsStrictlyPositive",a),Call("Nonnegative",c)),
            Equal(Call("subtract",Call("operatorLog",Call("addScalarIdentity",a,c)),Call("operatorLog",a)),
                Call("operatorLog",Call("add",D(1),Call("realSmul",c,Call("ringInverse",a)))))));
    }
    private static Formula ParameterOrder()
    {
        Formula a=F.Id("a"),b=F.Id("b");
        return HAll([V("a",F.Id("Real")),V("b",F.Id("Real")),V("P",Op),V("Q",Op)],
            Implies(And(Call("Positive",a),And(Le(a,b),And(Call("Nonnegative",P),Le(P,Q)))),
                Le(Call("orderedIncrement",b,P,Q),Call("orderedIncrement",a,P,Q))));
    }
    private static Formula Semicontinuity()=>HAll([V("P",Ref),V("Q",Ref)],
        Call("LowerSemicontinuous",Call("orderedEnergy",P,Q)));
    private static Formula GlobalIdentity()=>HAll([V("P",Ref),V("Q",Ref),V("rho",Tc)],
        Implies(And(Le(Call("operator",P),Call("operator",Q)),Call("Nonnegative",R)),
            Equal(Call("spectralEnergy",P,R),Call("add",Call("orderedEnergy",P,Q,R),Call("spectralEnergy",Q,R)))));
    private static Formula EqualReferences()=>HAll([V("P",Ref),V("rho",Tc)],Equal(Call("orderedEnergy",P,P,R),D(0)));
    private static DocumentBlock Item(string name,string title,Formula formula,string text)=>Describe.Lean(
        DescribeId.Create("ordered-"+name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy."+name),H(title),StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula All(Formula.BoundVariable[] xs,Formula body)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],body);
}
