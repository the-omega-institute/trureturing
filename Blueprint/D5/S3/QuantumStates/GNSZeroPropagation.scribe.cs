using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class GNSZeroPropagationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive normalized matrix trace functional propagates a zero quadratic value to every mixed value.",
        H("Zero Norm Propagation for Matrix States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-matrix-functional-cross-trace-factorization"),
                DeclarationHandle.Create("D5/S3/QuantumStates/GNSZeroPropagation.cross_trace_factorization"),
                H("The mixed trace is a Gram pairing after multiplication by the square root"),
                StatementSource.FromAuthor(Disp(CrossTraceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive semidefinite matrix rho and arbitrary matrices h and g, the trace pairing of rho with the conjugate transpose of h times g equals the Gram trace of h times the positive square root of rho and g times that square root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-matrix-functional-zero-norm-propagation"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/GNSZeroPropagation."
                        + "gns_zero_norm_propagation"),
                H("A zero quadratic value annihilates every mixed value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, Rho, Comma, Sp, F.Id("g"), Sp, InMacro, Sp,
                    Call("Matrix", F.Id("d"), F.Id("d"), Mathbb, Grp(F.Id("C"))), Comma, Esc,
                    Call("PosSemidef", Rho), Sp, Land, Sp,
                    Call("trace", Rho), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Call("stateFunctional", Rho,
                        Seq(F.Id("g"), Caret, Grp(Star), Sp, F.Id("g"))), Sp, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("h"), Sp, InMacro, Sp,
                    Call("Matrix", F.Id("d"), F.Id("d"), Mathbb, Grp(F.Id("C"))), Comma, Esc,
                    Call("stateFunctional", Rho,
                        Seq(F.Id("h"), Caret, Grp(Star), Sp, F.Id("g"))), Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state functional is the source trace pairing Tr(rho times a), with rho positive semidefinite and trace one. Its quadratic value at g is the squared Frobenius norm of g times the positive square root of rho.")),
                    Paragraph(Text(
                        "A zero quadratic value therefore makes g times the square root of rho equal to zero. The same factorization for an arbitrary h proves the mixed trace value Tr(rho h star g) is zero.")),
                    Paragraph(Text(
                        "The matrix GNS identity is reused directly; the deposited statement retains positivity, normalization, and the universal mixed-value conclusion as public clauses."))),
                DescribeRole.Theorem))));

    private static Formula CrossTraceFormula()
    {
        Formula Name(params string[] parts) => Seq(Operatorname,
            Grp(Seq([.. parts.SelectMany((part, index) => index == 0
                ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
        Formula Apply(Formula function, params Formula[] arguments) =>
            new Formula.Apply(function, [.. arguments]);
        Formula All(string name, Formula type, Formula body) =>
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        Formula Product(Formula left, Formula right) =>
            new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
        Formula Adj(Formula matrix) => Apply(Name("Matrix", "conjTranspose"), matrix);
        var d = F.Id("d");
        var rho = F.Id("rho");
        var h = F.Id("h");
        var g = F.Id("g");
        var matrix = Apply(Name("Matrix"), d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var root = Apply(Name("CFC", "sqrt"), rho);
        var equation = new Formula.Relation(
            Apply(Name("D5", "S3", "QuantumStates", "GNSZeroPropagation", "stateFunctional"),
                rho, Product(Adj(h), g)),
            FormulaRelationOperator.Equal,
            Apply(Name("Matrix", "trace"), Product(Adj(Product(h, root)), Product(g, root))));
        var implication = new Formula.Logic(Apply(Name("Matrix", "PosSemidef"), rho),
            FormulaLogicOperator.Implies, equation);
        return All("d", Name("Type"), Seq(
            OpenBracket, Apply(Name("Fintype"), d), CloseBracket,
            OpenBracket, Apply(Name("DecidableEq"), d), CloseBracket,
            All("rho", matrix, All("h", matrix, All("g", matrix, implication)))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
