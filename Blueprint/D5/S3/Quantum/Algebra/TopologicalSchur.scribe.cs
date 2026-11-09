using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class TopologicalSchurDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selfadjoint operator in the commutant of a topologically irreducible operator set is scalar.",
        H("Selfadjoint topological Schur"),
        Blocks(Describe.Lean(DescribeId.Create("selfadjoint-topological-schur"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/TopologicalSchur.exists_eq_algebraMap_of_isSelfAdjoint_of_commute"),
            H("Scalarity from closed invariant subspaces"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/suzuki2025topologicalschur")),
            Blocks(Paragraph(Text("H is any complete complex inner-product space, including the zero space. S is any set of bounded complex-linear operators. Topological irreducibility requires each closed complex-linear S-invariant subspace to be zero or all of H. If the bounded selfadjoint operator y commutes with every member of S, it is a real multiple of the identity. No finite-dimensional or algebraic irreducibility premise is imposed.")),
                Paragraph(Text("This is the immutable upstream theorem of Keisuke Suzuki cited below. The continuous functional calculus would separate distinct spectral points by two nonzero operators with disjoint support. The kernel of one is then a nontrivial proper closed S-invariant subspace. Thus the spectrum has one point, which yields the real scalar. The upstream definition and proof are reused with their original declaration names and license."))),
            DescribeRole.Theorem))));
    private static Formula C(string s, params Formula[] a) => global::StrataLint.Scribe.DefinitionDsl.Call(s,a);
    private static Formula I(string s) => F.Id(s);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Statement()
    {
        var h=I("H"); var s=I("S"); var y=I("y"); var t=I("T"); var r=I("r");
        var op=C("BoundedOperators",h);
        var commutes=All("T",op,Imp(C("Member",t,s),C("Commute",y,t)));
        var premises=And(C("IsTopologicallyIrreducible",s),And(C("IsSelfAdjoint",y),commutes));
        var conclusion=Ex("r",C("Real"),Equal(y,C("algebraMap",C("Real"),op,r)));
        var statement=All("S",C("Set",op),All("y",op,Imp(premises,conclusion)));
        return All("H",C("Type"),Imp(C("ComplexHilbert",h),statement));
    }
}
