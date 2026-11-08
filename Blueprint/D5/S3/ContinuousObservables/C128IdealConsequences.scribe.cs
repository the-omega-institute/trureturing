using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class C128IdealConsequencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local sections of the whole ideal prove nonunitality and detect ambient Jordan annihilation.",
        H("Whole-Ideal Local Sections and Nonunitality"), Blocks(
            Describe.Lean(DescribeId.Create("nonzero-nonunital"),
                DeclarationHandle.Create("D5/S3/ContinuousObservables/C128IdealConsequences.nonzero_nonunital"),
                H("The algebra is nonzero and genuinely nonunital"),
                StatementSource.FromAuthor(Disp(And(
                    Seq(Exists, Sp, V("r"), Colon, Sp, V("I"), Comma, Sp, V("r"), Neq, Sp, D(0)),
                    Seq(Exists, Sp, V("f"), Colon, Sp, V("A"), Comma, Sp, V("f"), Neq, Sp, D(0)),
                    Seq(Neg, Sp, Exists, Sp, V("e"), Colon, Sp, V("A"), Comma, Sp,
                        All("f", V("A"), And(Seq(V("e"), V("f"), Eq, V("f")), Seq(V("f"), V("e"), Eq, V("f")))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A is the whole complex C0 algebra on U=(0,1/4) minus every 1/n for n at least 5, with the genuine two by two matrix operator norm. The whole selfadjoint ideal I has a nonzero element, A has a nonzero element, and no element is a left and right multiplicative identity on all of A.")),
                    Paragraph(Text("Compactly supported local unit sections exist at every point of U. Symmetrizing one gives a selfadjoint section whose value there is the full matrix identity. A two-sided unit would therefore equal the identity at every point of U. The points 1/4-1/(40(n+1)) all lie in U and approach 1/4. Continuity of the whole zero extension then forces its value at 1/4 to be both zero and the matrix identity, a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("annihilator-on-whole-ideal"),
                DeclarationHandle.Create("D5/S3/ContinuousObservables/C128IdealConsequences.annihilator_iff"),
                H("Whole-ideal annihilation is pointwise vanishing"),
                StatementSource.FromAuthor(Disp(All("a", V("X"), Seq(
                    Par(All("r", V("I"), Seq(Call("S", V("a"), V("r")), Eq, D(0)))),
                    Iff, Sp, All("t", V("U"), Seq(Call("a", Call("inc", V("t"))), Eq, D(0))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("X is the whole selfadjoint continuous matrix field space on [0,1], I is its entire zero-off-U selfadjoint ideal, S(a,r)=(ar+ra)/2, and inc includes U in [0,1]. For every a in X, annihilating every element of I under S is equivalent to vanishing at every point of U.")),
                    Paragraph(Text("The inverse of the onto real linear isometry j carries each selfadjoint local identity section into the whole ideal I. Evaluating S(a,r)=0 at that point gives a=0 there. Conversely the product is zero on U because a vanishes there, and off U because every ideal field vanishes there. This establishes the ambient pointwise criterion; identifying the closure of U with [0,1/4] and the original polynomial-domain annihilator requires further arguments."))),
                DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((c, i) =>
        i == 0 ? new Formula[] { Par(c) } : new Formula[] { Sp, Land, Sp, Par(c) }).ToArray());
}
