using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class WuUnequalTemperatureCoherenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two CAR modes at unequal inverse temperatures can exceed both single-mode rank-one gains.",
        H("Unequal-temperature CAR coherence"),
        Blocks(
            Theorem("wu-unequal-temperature-car", "car", "The hole lowering matrices",
                StatementSource.WithoutFormula(),
                "In empty, first, second, both hole order, the first matrix has unit entries at (0,1) and (2,3). " +
                "The second has entries 1 at (0,2) and −1 at (1,3). All other entries vanish. " +
                "Each is the adjoint of the corresponding occupation lowering matrix reindexed by complementing " +
                "both occupation bits and putting the first hole bit second in the product index. " +
                "Their products Jᵢ†Jᵢ project onto the states with hole i present. " +
                "For a unit vector x, the expectation zᵢ = x†Jᵢx is the conjugate of the occupation lowering " +
                "expectation in the reindexed state, so their squared moduli agree."),
            Theorem("wu-unequal-temperature-certificate", "physical_certificate", "Exact witness and axis optima",
                StatementSource.WithoutFormula(),
                "At source exponent two, take β = 8 log 2 and the two mode parameters (4 log 2, 8 log 2). " +
                "Equations (3.54) and (3.55) of Wu v1 give α₂*(β) = 2L. Set aᵢ = 1/(1+exp βᵢ), " +
                "bᵢ = 1−aᵢ and T = Tr(M²) for the Gibbs-embedded positive input M. On the rank-one " +
                "density M²/T, the two transported jump traces for mode i both equal |zᵢ|². Its contribution " +
                "to the entropy divided by T is −log bᵢ + βᵢqᵢ. Subtracting the entropy term from the energy " +
                "gives the deficit divided by 2T as ∑ᵢ(aᵢ + L log bᵢ) − ∑ᵢ(cᵢ|zᵢ|² − dᵢqᵢ). " +
                "This identity uses the continuous extension to rank-one positive inputs. " +
                "With L = (cosh(β/2) − 1)/(β sinh(β/2)), the coefficients cᵢ = sech(βᵢ/2) and " +
                "dᵢ = tanh(βᵢ/2) − L βᵢ are (8/17, 32/257) and (15/34, 480/4369), respectively. " +
                "The unit vector (60,9,10,1)/√3782 has hole probabilities (82,101)/3782 and " +
                "lowering expectations (550,591)/3782. Its total gain ∑ᵢ(cᵢ|zᵢ|² − dᵢqᵢ) is " +
                "15416747/31246048178 > 49/100000. For each mode, |zᵢ|² ≤ qᵢ(1 − qᵢ) by Cauchy–Schwarz. " +
                "A superposition of the hole vacuum and the corresponding one-hole vector attains equality " +
                "at qᵢ = (cᵢ − dᵢ)/(2cᵢ). Completing the square gives the exact maxima 1/2176 and 32/74273."),
            Theorem("wu-unequal-temperature-result", "result", "Failure of single-mode domination",
                StatementSource.FromAuthor(Disp(new Formula.Not(
                    new Formula.Symbol(FormulaIdentifier.Create("claim"))))),
                "The claim asks whether for each unit vector there is a mode and a unit vector whose gain " +
                "on that mode alone dominates the original total gain. Both single-mode maxima lie below " +
                "49/100000, so the exhibited unit vector refutes the claim at these two unequal temperatures."))));

    private static DocumentBlock Theorem(string id, string declaration, string title,
        StatementSource statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), statement, AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
