using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicityFormula;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal static class PermutationMultiplicityFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [..a]);
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula N => Seq(Mathbb,Grp(F.Id("N")));
    internal static Formula Type => V("Type");
    internal static Formula Perm(Formula q) => Call("Perm",q);
    internal static Formula Parts(Formula sigma) => Call("parts",Call("partition",sigma));
    internal static DocumentBlock.Describe Desc(string prefix,string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem,AssessedProvenance? provenance=null,OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role,
            openProblemResolutionClaim:resolution);
}

internal sealed class PermutationMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.";
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/tauceti2026classsizes"));
    private static Formula M => SF.V("m");
    private static Formula Z(Formula m) => SF.Call("z",m);
    private static Formula Counts(Formula m,Formula l) => SF.Call("count",m,l);
    private static Formula Term(Formula m,Formula l) => SF.Mul(SF.Pow(l,Counts(m,l)),SF.Call("factorial",Counts(m,l)));
    private static Formula Prod(Formula m,Formula s) => Seq(F.Prod,Underscore,Grp(SF.V("l"),InMacro,Sp,s),Sp,Term(m,SF.V("l")));
    public DocumentDefinition Create()
    {
        var sigma=SF.V("sigma");var c=SF.Call("cycleType",sigma);var a=SF.V("A");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The multiplicity factor of a full permutation partition includes its fixed-point factorial.",
            H("Full permutation multiplicities"),Blocks(
                SF.Desc(Prefix,"z","The multiplicity factor",SF.All("m",SF.Call("Multiset",SF.N),
                    SF.Eq(Z(M),Prod(M,SF.Call("toFinset",M)))),
                    "For a multiset m of natural numbers, z(m) is the product of l^(count_m(l)) times count_m(l)! over its distinct entries. "
                    + "This is the Tau Ceti full-partition normalization used in the distinct-cycle-size limit.",DescribeRole.Definition,Source),
                SF.Desc(Prefix,"hz_prod","Extending the finite product",SF.All("m",SF.Call("Multiset",SF.N),
                    SF.All("s",SF.Call("Finset",SF.N),SF.Imp(SF.Call("Subset",SF.Call("toFinset",M),SF.V("s")),
                        SF.Eq(Z(M),Prod(M,SF.V("s")))))),
                    "Any finite set containing the support gives the same product: missing entries have multiplicity zero and factor one.",provenance:Source),
                SF.Desc(Prefix,"hz_perm","Cycle type and fixed points",SF.All("A",SF.Type,SF.Imp(SF.Call("Fintype",a),SF.Imp(SF.Call("DecidableEq",a),
                    SF.All("sigma",SF.Perm(a),SF.Eq(Z(SF.Parts(sigma)),
                        SF.Mul(SF.Mul(SF.Call("factorial",SF.Call("tsub",SF.Call("FintypeCard",a),SF.Call("sum",c))),SF.Call("prod",c)),
                            SF.Call("MultiplicityFactorialProduct",c))))))),
                    "For every permutation of a finite carrier A, z(partition(sigma)) equals (card(A)-sum(cycleType(sigma)))! times prod(cycleType(sigma)) "
                    + "times the product of count(l)! over the distinct nontrivial cycle lengths. The omitted singleton cycles are restored by the first factorial. "
                    + "This normalization is adapted from Tau Ceti's symmetric-group partition and class-size development; the complete Apache 2.0 license is retained in the cited note.",provenance:Source)),[]));
    }
}
