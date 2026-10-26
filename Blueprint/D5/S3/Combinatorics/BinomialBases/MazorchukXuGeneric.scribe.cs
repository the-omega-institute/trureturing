using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuGenericNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuGenericNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

internal sealed class MazorchukXuGenericDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct positive position data and distinct cutoff-position pairs force the exceptional-edge choices.",
        H("Forced edges in generic patterns"),
        Blocks(
            Node("Generic","Position","Position relative to the ordinary list",PositionFormula(),
                "The zero-indexed list has M vertices. Exactly the indices below p occur before s, and exactly the indices at least p occur after s. The bound includes p=0 and p=M; no listed vertex equals s.",DescribeRole.Definition),
            Node("Generic","Cutoff","Incidence cutoff",CutoffFormula(),
                "The cutoff lies between zero and M. Incidence starts at the zero-indexed cutoff. Both empty and full incidence are included.",DescribeRole.Definition),
            Node("Generic","generic_exceptional_edge","The forced generic edge criterion",MainFormula(),
                "Assume the rules P and J, a list of vertices joined to zero, positions 0<ps<pt, and the two incidence cutoffs. When cs differs from pt and ct differs from ps, the edge from s to t exists exactly when cs<pt and ct<ps. Necessity uses the ordinary vertex just after s, then the vertices around t; when pt=M the latter bound follows directly from the cutoff bound. Sufficiency uses ordinary vertices immediately before s and t in J. No strict-monotonicity hypothesis on the list is needed because the position predicates already give the inequalities used in the proof. This criterion does not assert the existence or enumerate the admissible generic patterns.",DescribeRole.Theorem)), []));

    private static Formula PositionFormula()
    {
        var M=V("M");var g=V("g");var s=V("s");var p=V("p");var r=V("r");
        var conditions=And(Le(p,M),All("r",Fn("Fin",M),And(
            Iff(Lt(Fn("g",r),s),Lt(Fn("val",r),p)),
            Iff(Lt(s,Fn("g",r)),Le(p,Fn("val",r))))));
        return All("M",N,All("g",Map(Fn("Fin",M),N),Many("s p",N,
            Iff(Fn("Position",g,s,p),conditions))));
    }
    private static Formula CutoffFormula()
    {
        var M=V("M");var E=V("E");var g=V("g");var s=V("s");var c=V("c");var r=V("r");
        var conditions=And(Le(c,M),All("r",Fn("Fin",M),
            Iff(Fn("Incident",E,s,Fn("g",r)),Le(c,Fn("val",r)))));
        return All("M",N,All("E",Rel(N),All("g",Map(Fn("Fin",M),N),Many("s c",N,
            Iff(Fn("Cutoff",E,g,s,c),conditions)))));
    }
    private static Formula MainFormula()
    {
        var M=V("M");var E=V("E");var g=V("g");var s=V("s");var t=V("t");
        var ps=V("ps");var pt=V("pt");var cs=V("cs");var ct=V("ct");
        var hypothesis=And(Fn("Rules",E),All("r",Fn("Fin",M),Fn("E",D(0),Fn("g",V("r")))),
            Lt(D(0),ps),Lt(ps,pt),Fn("Position",g,s,ps),Fn("Position",g,t,pt),
            Fn("Cutoff",E,g,s,cs),Fn("Cutoff",E,g,t,ct),Not(Eq(cs,pt)),Not(Eq(ct,ps)));
        var conclusion=Iff(Fn("E",s,t),And(Lt(cs,pt),Lt(ct,ps)));
        return All("E",Rel(N),All("M",N,All("g",Map(Fn("Fin",M),N),
            Many("s t ps pt cs ct",N,Imp(hypothesis,conclusion)))));
    }
}
