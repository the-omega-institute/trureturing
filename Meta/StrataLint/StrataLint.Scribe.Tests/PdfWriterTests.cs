using System.Text;
using StrataLint.Scribe.Definitions;

namespace StrataLint.Scribe.Tests;

public sealed class PdfWriterTests
{
    [Fact]
    public void QuestPdfWriterGeneratesEachPilotWithAPdfHeader()
    {
        foreach (var pilot in PilotDocuments.All)
        {
            var pdf = QuestPdfWriter.Write(pilot.Document);

            Assert.True(pdf.Length > 5);
            Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
        }
    }
}
