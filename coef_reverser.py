COEFFS_ADDRESS = "input_files/coeffs.txt"
COEFFS_REVERSE_ADDRESS = "input_files/coeffs_reversed.txt"

coefFile = open(COEFFS_ADDRESS, 'r')
lines = coefFile.readlines()
lines.reverse()
coefFile.close()

newFile = open(COEFFS_REVERSE_ADDRESS, 'w')
newFile.writelines(lines)

print('done')