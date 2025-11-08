This module will take a binary string of a jpeg image, decompress it, and return the RGB values of the image. 
To use the module simply require it and call the function as follows:

    local DecodeJpeg = require(DecodeJpeg module path)
    local Info = DecodeJpeg(jpeg file name)

Note: it might be ideal to wrap the function in a pcall in case of an error during the decoding process
The returned dictionary will contain the following useful values:
 - X: the witdh of the image
 - Y: the height of the image
 - SamplePrecision: the number of bits used to represent the color values (usually always 8 and can be ignored)
 - Pixels: 2D array of the RGB values of the image the first index represents the color componant, 
		while the second represents the pixel.

For example Info may have the following values:

    X = 2
    Y = 2
		Pixels = {{255, 255, 255, 255} {0, 0, 0, 0}, {100, 100, 100, 100}}
		
Pixels[1] is the red values, Pixels[2] is the green values and Pixels[3] is the blue values
		
The array for the color componant is represented as a 1D array of the pixels in order from left to right and top 
to bottom (ex. notice the index Pixels[1][3] gives the red value for row 2 column 1 of the image).
