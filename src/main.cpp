#include "./include/mainwindow.h"

#include <QApplication>

int main(int argc, char *argv[])
{
    std::cout << "fuck qt" << "\n";
    QApplication a(argc, argv);
    MainWindow w;
    w.show();
    return a.exec();
    __cplusplus;
}
