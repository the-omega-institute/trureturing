using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact integer certificate for the 59-coordinate terminal vector gives an annihilator at every nonnegative shift.",
        H("The quotient terminal-vector annihilator"),
        Blocks(
            N("rows", "The sparse matrix", "The list at each of the 59 rows contains its nonzero column-and-integer-weight pairs. These are the 207 nonzero entries of the supplied quotient certificate."),
            N("terminal", "The terminal vector", "The 59 integer terminal values form the zeroth vector."),
            N("values", "Finite power certificate", "All 49 vectors, indexed from exponent 0 through 48, are literal exact integers. They are certificate inputs, not assumed powers."),
            N("denominator", "The entire denominator", "The 49 coefficients in increasing degree order are exactly those of Colin Barker's denominator in OEIS A286848, https://oeis.org/A286848. Its constant coefficient is 1 and its degree is 48. Attribution and CC-BY-SA-4.0 apply to the reproduced formula: https://creativecommons.org/licenses/by-sa/4.0/."),
            N("step", "Integer linear multiplication", "Sparse row evaluation is packaged as an integer linear map, so sums and integer scalar multiples commute with each matrix step."),
            T("power_steps", "Check every successive vector", "For every k in Fin 48 and every i in Fin 59, step(values(k.castSucc))(i) = values(k.succ)(i). Kernel decisions verify every coordinate."),
            T("initial_vector", "Check the initial vector", "values(0) = terminal. The equality is definitional."),
            T("finite_annihilator", "Check all residual coordinates", "For every i in Fin 59, the sum over j in Fin 49 of denominator(j) times values(48-j)(i) is zero. Every one of the 59 coordinates is kernel checked."),
            N("orbit", "The unrestricted matrix orbit", "orbit(0) = terminal and orbit(k+1) = step(orbit(k)) for every natural k."),
            T("shifted_annihilator", "Every shift", "For every natural k, the vector sum over j in Fin 49 of denominator(j) scalar-multiplying orbit(k+48-j) is zero. Induction applies the linear map to the previous zero residual; the conclusion is not extrapolated from finite agreement."),
            Paragraph(Text("The supplied numerical certificate has SHA-256 ab0c5370648ec80cad7798774a9ce6ad7cf62b7d34f296441e3a897715f0701c. The total transfer partition identifies the full and quotient orbits through TR=RB, f=Rg and betaR=alpha. Evaluation against alpha then transports this vector annihilator to the actual subset counts; the complete initial numerator convolutions fix every remaining coefficient."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock T(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bq-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
