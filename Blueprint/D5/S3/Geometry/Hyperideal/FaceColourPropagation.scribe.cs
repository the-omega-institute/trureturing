using System;
using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FaceColourPropagationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FaceColourPropagation.balanced_signature_constant";

    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Opposite-paired global edge colours force one local type on each connected face-paired component.",
        H("A face signature prevents mixing the balanced local types"),
        Blocks(
            Paragraph(Text("T and E are arbitrary types. Incidence s specifies six global edge "
                + "labels per tetrahedron and one Boolean low colour per global label. "
                + "FacePairing(s) specifies an involutive partner map on T x Fin(4), a permutation "
                + "of the three edges of each face, and equality of the corresponding global "
                + "edge labels. Connected means every pair of tetrahedra is linked by a finite "
                + "path of these face steps, expressed using Relation.ReflTransGen.")),
            Paragraph(Text("The local edge order is (12,13,14,34,24,23). Balanced(s) means "
                + "opposite slots 0,3 have equal colour, as do 1,4 and 2,5. The indicator mark "
                + "has value one on low labels and zero on high labels. P(s,t) is mark at slots "
                + "0,1,2 summed, which is the number of low opposite pairs under Balanced. "
                + "F(s,t,f) is the count of low edge occurrences on face f. The four face "
                + "edge lists are (3,4,5), (1,2,3), (0,2,4), and (0,1,5).")),
            Describe.Lean(DescribeId.Create("balanced-face-signature-constant"),
                DeclarationHandle.Create(Declaration),H("One signature throughout a connected pairing"),
                StatementSource.FromAuthor(F.Disp(Statement())),AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Opposite colour equalities identify each face sum with P(s,t). "
                        + "The face-pairing equation preserves all three actual edge labels, and "
                        + "permuting the three summands preserves their sum. Thus paired faces "
                        + "have equal signatures. Induction along the finite face path propagates "
                        + "the equality to any two tetrahedra. Equality of neighbouring pair counts "
                        + "is derived from the gluing; it is not a hypothesis.")),
                    Paragraph(Text("The four balanced types have P=0,1,2,3: all high, one low "
                        + "opposite pair, one low four-cycle, and all low. Consequently the one-pair "
                        + "and four-cycle types cannot coexist in a connected complex using only "
                        + "balanced types. A transition requires at least one tetrahedron with "
                        + "unequal colours on some opposite pair. This does not rule out general "
                        + "mixed-valence triangulations or refute CFMP.")),
                    Paragraph(Text("The theorem is independent of lengths, curvature and "
                        + "manifold-link certification. It applies even to infinite carriers "
                        + "when the stated finite-path connectedness holds. Finite colour-pattern "
                        + "checks are diagnostics; the global proof does not enumerate complexes."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var s=F.Id("s");var p=F.Id("p");var t=F.Id("t");var u=F.Id("u");var f=F.Id("f");
        var local=All([("t",F.Id("T")),("f",Call("Fin",F.D(4)))],
            Eq(Call("F",s,t,f),Call("P",s,t)));
        var global=All([("t",F.Id("T")),("u",F.Id("T"))],
            Eq(Call("P",s,t),Call("P",s,u)));
        return All([("T",F.Id("Type")),("E",F.Id("Type")),
            ("s",Call("Incidence",F.Id("T"),F.Id("E"))),("p",Call("FacePairing",s))],
            Imp(Call("Balanced",s),Imp(Call("Connected",p),
                new Formula.Logic(local,FormulaLogicOperator.And,global))));
    }
    private static Formula All((string Name,Formula Type)[] variables,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..variables.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Call(string name,params Formula[] args)
    {
        var p=new List<Formula>{F.Operatorname,F.Grp(F.Id(name)),F.Open};
        for(var i=0;i<args.Length;i++){if(i>0)p.AddRange([F.Comma,F.Sp]);p.Add(args[i]);}
        p.Add(F.Close);return F.Seq([..p]);
    }
}
