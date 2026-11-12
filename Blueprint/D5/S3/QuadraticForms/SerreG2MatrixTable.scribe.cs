using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SerreG2MatrixTableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/SerreG2MatrixTable.";
    public DocumentDefinition Create()
    {
        var basisType = All(X("i"), Fin14, Call("Matrix", Call("Fin", D(7)), Call("Fin", D(7)), Call("Int")));
        var coefficientType = All(X("i"), Fin14, All(X("j"), Fin14, new Formula.TypeArrow(Fin14, Call("Int"))));
        var combination = Call("Finset.sum", Call("Finset.univ"), Seq(Open, X("fun"), Sp, X("t"), Sp, Mapsto, Sp,
            Call("zsmul", Call("coefficients", X("i"), X("j"), X("t")), Call("basisMatrix", X("t"))), Close));
        var bracket = All(X("i"), Fin14, All(X("j"), Fin14,
            Eq(Call("lie", Call("basisMatrix", X("i")), Call("basisMatrix", X("j"))), combination)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Integral matrices for the standard seven-dimensional G2 representation.", H("Integral G2 matrix relations"), Blocks(
                Entry("basisMatrix", "Fourteen integral matrices", basisType,
                    "Two coroot matrices and six positive and six negative root matrices are given with integer entries. They are classical representation data. They do not define the standard Serre object or assume its dimension.", DescribeRole.Definition),
                Entry("coefficients", "Integral bracket coefficients", coefficientType,
                    "The integral structure constants describe each commutator in the fourteen matrices. The complete table is consumed by the scalar-extension and actual Serre-correspondence proof.", DescribeRole.Definition),
                Entry("bracket", "Kernel-checked integral bracket identities", bracket,
                    "Every matrix identity is proved by Lean kernel reduction of its scalar entries. External code only generated the candidate data. The companion module transports these identities to every characteristic-zero field and constructs the genuine Serre map. These are classical G2 facts, with the KMV application credited to Haobo Ma then Wenlin Zhang; no priority is claimed.", DescribeRole.Theorem))));
    }
    private static Formula Fin14 => Call("Fin", D(1,4));
    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part,i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [..xs]);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall,Sp,Open,x,Sp,Colon,Sp,t,Close,Comma,Sp,Open,b,Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
}
